package org.scalameta.paradise
package typechecker

import org.scalameta.paradise.converters.Converter
import org.scalameta.paradise.parser.SyntaxAnalyzer

import scala.meta.Term
import scala.meta.dialects.Paradise211

trait Expanders extends Converter { self: AnalyzerPlugins =>

  import scala.util.control.ControlThrowable
  import global._
  import analyzer._
  import ErrorUtils._
  import definitions._
  import scala.reflect.internal.Flags._
  import scala.reflect.internal.Mode._
  import scala.reflect.runtime.ReflectionUtils
  import analyzer.{Namer => NscNamer}
  import scala.{meta => m}
  import scala.meta.{Input => MetaInput, Position => MetaPosition}
  import scala.meta.internal.prettyprinters.{Positions => MetaPositions}

  def mkExpander(namer0: NscNamer) = new { val namer: NscNamer = namer0 } with Namer with Expander
  trait Expander { self: Namer with Expander =>

    val namer: NscNamer
    import namer._
    val expanderErrorGen = new ErrorGen(namer.typer)
    import expanderErrorGen._
    import namer.typer.TyperErrorGen._

    def expandOldAnnotationMacro(original: Tree,
                                 annotationSym: Symbol,
                                 annotationTree: Tree,
                                 expandees: List[Tree]): Option[List[Tree]] = {
      def onlyIfExpansionAllowed[T](expand: => Option[T]): Option[T] = {
        if (settings.Ymacroexpand.value == settings.MacroExpand.None) None
        else {
          val oldYmacroexpand = settings.Ymacroexpand.value
          try { settings.Ymacroexpand.value = settings.MacroExpand.Normal; expand } catch {
            case ex: Exception => settings.Ymacroexpand.value = oldYmacroexpand; throw ex
          }
        }
      }
      def expand(): Option[Tree] = {
        def rollThroughImports(context: Context): Context = {
          if (context.isInstanceOf[ImportContext]) rollThroughImports(context.outer)
          else context
        }
        val typer = {
          // expanding at top level => allow the macro to see everything
          if (original.symbol.isTopLevel) newTyper(context)
          // expanding at template level => only allow to see outside of the enclosing class
          // we have to skip two contexts:
          //  1) the Template context that hosts members
          //  2) the ImplDef context that hosts type params (and just them?)
          // upd. actually, i don't think we should skip the second context
          // that doesn't buy us absolutely anything wrt robustness
          else if (original.symbol.owner.isClass) newTyper(rollThroughImports(context).outer)
          // expanding at block level => only allow to see outside of the block
          else newTyper(rollThroughImports(context).outer)
        }
        val expandee = {
          val annotationMacroSym = annotationSym.info.member(nme.macroTransform)
          val prefix =
            Select(annotationTree, nme.macroTransform)
              .setSymbol(annotationMacroSym)
              .setPos(annotationTree.pos)
          Apply(prefix, expandees) setPos annotationTree.pos
        }
        (new DefMacroExpander(typer, expandee, NOmode, WildcardType) {
          override def onSuccess(expanded: Tree) = expanded
        })(expandee) match {
          case tree if tree.isErroneous => None
          case tree => Some(tree)
        }
      }
      extractAndValidateExpansions(original,
                                   annotationTree,
                                   () => onlyIfExpansionAllowed(expand()))
    }

    def expandNewAnnotationMacro(original: Tree,
                                 annotationSym: Symbol,
                                 annotationTree: Tree,
                                 expandees: List[Tree]): Option[List[Tree]] = {
      def expand(): Option[Tree] = {
        try {
          val metaArgs = {
            val prefixArg = annotationTree.toMtree[m.Term.New]
            val targsArgs = {
              val Apply(Select(New(tpt), nme.CONSTRUCTOR), _) = annotationTree
              val expectedTargs = annotationSym.typeParams
              val actualTargs = tpt match {
                case AppliedTypeTree(_, targs) => targs
                case _ => Nil
              }
              if (expectedTargs.length != actualTargs.length) {
                val message =
                  MacroAnnotationTargMismatch(annotationSym, expectedTargs, actualTargs)
                issueNormalTypeError(annotationTree, message)(namer.context)
                throw MacroExpansionException
              }
              actualTargs.map(_.toMtree[m.Type])
            }
            val vargssArgs = {
              // NOTE: Value arguments of macro annotations are passed in the prefix.
              // See the discussion at https://github.com/scalameta/paradise/issues/11 for more details.
              Nil
            }
            val expandeesArg = expandees.map(_.toMtree[m.Stat]) match {
              case Nil =>
                abort(
                  "Something unexpected happened. Please report to https://github.com/scalameta/paradise/issues.")
              case tree :: Nil => tree
              case list @ _ :: tail => m.Term.Block(list.asInstanceOf[List[m.Stat]])
            }
            List(prefixArg) ++ targsArgs ++ vargssArgs ++ List(expandeesArg)
          }
          val classloader = {
            val m_findMacroClassLoader =
              analyzer.getClass.getMethods().find(_.getName == "findMacroClassLoader").get
            m_findMacroClassLoader.setAccessible(true)
            m_findMacroClassLoader.invoke(analyzer).asInstanceOf[ClassLoader]
          }
          val annotationModuleClass = {
            val annotationModule =
              annotationSym.owner.info.decl(annotationSym.name.inlineModuleName)
            val annotationModuleClassName = {
              // TODO: Copy/pasted from Macros.scala. I can't believe there's no better way of doing this.
              def loop(sym: Symbol): String = sym match {
                case sym if sym.isTopLevel =>
                  val suffix = if (sym.isModule || sym.isModuleClass) "$" else ""
                  sym.fullName + suffix
                case sym =>
                  val separator = if (sym.owner.isModuleClass) "" else "$"
                  loop(sym.owner) + separator + sym.javaSimpleName.toString
              }
              loop(annotationModule)
            }
            try Class.forName(annotationModuleClassName, true, classloader)
            catch {
              case ex: Throwable =>
                issueNormalTypeError(annotationTree, MacroAnnotationNotExpandedMessage)(
                  namer.context)
                throw MacroExpansionException
            }
          }
          val annotationModule = annotationModuleClass.getField("MODULE$").get(null)
          val newStyleMacroMeth = annotationModuleClass
            .getDeclaredMethods()
            .find(_.getName == InlineAnnotationMethodName.inlineImplName.toString)
            .get
          newStyleMacroMeth.setAccessible(true)
          val metaExpansion = {
            macroExpandWithRuntime({
              try {
                newStyleMacroMeth
                  .invoke(annotationModule, metaArgs.asInstanceOf[List[AnyRef]].toArray: _*)
                  .asInstanceOf[m.Tree]
              } catch {
                case ex: Throwable =>
                  val realex = ReflectionUtils.unwrapThrowable(ex)
                  realex match {
                    case ex: ControlThrowable => throw ex
                    case _ => MacroGeneratedException(annotationTree, realex)
                  }
              }
            })
          }

          val stringExpansion = metaExpansion match {
            case b: Term.Block => Paradise211(b).syntax.stripPrefix("{").stripSuffix("}")
            case a => Paradise211(a).syntax
          }

          val compiler = new { val global: Expanders.this.global.type = Expanders.this.global }
          with SyntaxAnalyzer
          val parser =
            compiler.newUnitParser(new CompilationUnit(newSourceFile(stringExpansion, "<macro>")))
          val expandedTree = gen.mkTreeOrBlock(parser.parseStatsOrPackages())
          removeAllRangePositions(expandedTree)
          Some(expandedTree)
        } catch {
          // NOTE: this means an error that has been caught and reported
          case MacroExpansionException => None
        }
      }
      extractAndValidateExpansions(original, annotationTree, () => expand())
    }

    // NOTE: this method is here for correct stacktrace unwrapping
    // the name, the position in the file and the visibility are all critical
    private def macroExpandWithRuntime[T](body: => T): T = body

    private def extractAndValidateExpansions(
        original: Tree,
        annotation: Tree,
        computeExpansion: () => Option[Tree]): Option[List[Tree]] = {
      val sym = original.symbol
      val companion =
        if (original.isInstanceOf[ClassDef] || original.isInstanceOf[TypeDef]) {
          patchedCompanionSymbolOf(sym, context)
        } else {
          NoSymbol
        }
      val wasWeak = isWeak(companion)
      val wasTransient = companion == NoSymbol || companion.isSynthetic
      def extract(expanded: Tree): List[Tree] = expanded match {
        case Block(stats, Literal(Constant(()))) => stats // ugh
        case tree => List(tree)
      }
      def validate(expanded: List[Tree]): Option[List[Tree]] = {
        if (sym.owner.isPackageClass) {
          original match {
            case ClassDef(_, originalName, _, _) =>
              expanded match {
                case (expandedClass @ ClassDef(_, className, _, _)) :: Nil
                    if className == originalName && wasWeak =>
                  attachExpansion(sym, List(expandedClass))
                  attachExpansion(companion, Nil)
                  Some(expanded)
                case (expandedCompanion @ ModuleDef(_, moduleName, _)) ::
                      (expandedClass @ ClassDef(_, className, _, _)) :: Nil
                    if className == originalName && moduleName == originalName.toTermName =>
                  attachExpansion(
                    sym,
                    if (wasWeak) List(expandedClass, expandedCompanion) else List(expandedClass))
                  attachExpansion(companion, List(expandedCompanion))
                  Some(expanded)
                case (expandedClass @ ClassDef(_, className, _, _)) ::
                      (expandedCompanion @ ModuleDef(_, moduleName, _)) :: Nil
                    if className == originalName && moduleName == originalName.toTermName =>
                  attachExpansion(
                    sym,
                    if (wasWeak) List(expandedClass, expandedCompanion) else List(expandedClass))
                  attachExpansion(companion, List(expandedCompanion))
                  Some(expanded)
                case _ =>
                  if (wasWeak) MacroAnnotationTopLevelClassWithoutCompanionBadExpansion(annotation)
                  else MacroAnnotationTopLevelClassWithCompanionBadExpansion(annotation)
                  None
              }
            case ModuleDef(_, originalName, _) =>
              expanded match {
                case (expandedModule @ ModuleDef(_, expandedName, _)) :: Nil
                    if expandedName == originalName =>
                  attachExpansion(sym, List(expandedModule))
                  Some(expanded)
                case _ =>
                  MacroAnnotationTopLevelModuleBadExpansion(annotation)
                  None
              }
          }
        } else {
          if (wasTransient) {
            attachExpansion(sym, expanded)
            attachExpansion(companion, Nil)
          } else {
            def companionRelated(tree: Tree) =
              tree.isInstanceOf[ModuleDef] && tree.asInstanceOf[ModuleDef].name == companion.name
            val (forCompanion, forSym) = expanded.partition(companionRelated)
            attachExpansion(sym, forSym)
            attachExpansion(companion, forCompanion)
          }
          Some(expanded)
        }
      }
      for {
        lowlevelExpansion <- computeExpansion()
        expansion <- Some(extract(lowlevelExpansion))
        duplicated = expansion.map(duplicateAndKeepPositions)
        validatedExpansion <- validate(duplicated)
      } yield validatedExpansion
    }

    def expandMacroAnnotations(stats: List[Tree]): List[Tree] = {
      def mightNeedTransform(stat: Tree): Boolean = stat match {
        case stat: DocDef => mightNeedTransform(stat.definition)
        case stat: MemberDef => isMaybeExpandee(stat.symbol) || hasAttachedExpansion(stat.symbol)
        case _ => false
      }
      def rewrapAfterTransform(stat: Tree, transformed: List[Tree]): List[Tree] =
        (stat, transformed) match {
          case (stat @ DocDef(comment, _), List(transformed: MemberDef)) =>
            List(treeCopy.DocDef(stat, comment, transformed))
          case (stat @ DocDef(comment, _), List(transformed: DocDef)) => List(transformed)
          case (_, Nil | List(_: MemberDef)) => transformed
          case (_, unexpected) =>
            unexpected // NOTE: who knows how people are already using macro annotations, so it's scary to fail here
        }
      if (phase.id > currentRun.typerPhase.id || !stats.exists(mightNeedTransform)) stats
      else
        stats.flatMap(stat => {
          if (mightNeedTransform(stat)) {
            val sym = stat.symbol
            assert(sym != NoSymbol, (sym, stat))
            if (isMaybeExpandee(sym)) {
              def assert(what: Boolean) =
                Predef.assert(
                  what,
                  s"${sym.accurateKindString} ${sym.rawname}#${sym.id} with ${sym.rawInfo.kind}")
              assert(sym.rawInfo.isInstanceOf[Namer#MaybeExpandeeCompleter])
              sym.rawInfo.completeOnlyExpansions(sym)
              assert(!sym.rawInfo.isInstanceOf[Namer#MaybeExpandeeCompleter])
            }
            val derivedTrees = attachedExpansion(sym).getOrElse(List(stat))
            val (me, others) = derivedTrees.partition(_.symbol == sym)
            rewrapAfterTransform(stat, me) ++ expandMacroAnnotations(others)
          } else {
            List(stat)
          }
        })
    }
  }
}
