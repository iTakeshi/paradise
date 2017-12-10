package org.scalameta.paradise
package converters

import scala.collection.{immutable, mutable}
import scala.reflect.{classTag, ClassTag}
import scala.compat.Platform.EOL
import scala.meta.prettyprinters._
import scala.{meta => m}

trait ToMtree { self: Converter =>

  protected implicit class XtensionGtreeToMtree(gtree: g.Tree) {
    def toMtree[T <: m.Tree: ClassTag]: T = self.toMtree[T](gtree)
  }

  private def toMtree[T <: m.Tree: ClassTag](gtree: g.Tree): T = {
    object l extends LogicalTrees[g.type](g, gtree)

    object toMtree {
      implicit class XtensionGtreeToMtree(gtree0: g.Tree) {
        def toMtree[T <: m.Tree: ClassTag]: T = {
          wrap[T](gtree0, (gtree, gexpansion) => {
            val mtree = gtree match {
              // ============ NAMES ============

              case l.AnonymousName() =>
                m.Name.Anonymous()

              case l.IndeterminateName(lvalue) =>
                m.Name.Indeterminate(lvalue)

              // ============ TERMS ============

              case l.TermThis(lname) =>
                val mname = lname.toMtree[m.Name]
                m.Term.This(mname)

              case l.TermSuper(lthis, lsuper) =>
                val mthis = lthis.toMtree[m.Name]
                val msuper = lsuper.toMtree[m.Name]
                m.Term.Super(mthis, msuper)

              case l.TermName(lvalue) =>
                m.Term.Name(lvalue)

              case l.TermIdent(lname) =>
                lname.toMtree[m.Term.Name]

              case l.TermSelect(lpre, lname) =>
                val mpre = lpre.toMtree[m.Term]
                val mname = lname.toMtree[m.Term.Name]
                m.Term.Select(mpre, mname)

              case l.TermInterpolate(lprefix, lparts, largs) =>
                val mprefix = lprefix.toMtree[m.Term.Name]
                val mparts = lparts.toMtrees[m.Lit]
                val margs = largs.toMtrees[m.Term]
                m.Term.Interpolate(mprefix, mparts, margs)

              case l.TermApply(lfun, largs) =>
                val mfun = lfun.toMtree[m.Term]
                val margs = largs.toMtrees[m.Term]
                m.Term.Apply(mfun, margs)

              case l.TermApplyInfix(llhs, lop, ltargs, largs) =>
                val mlhs = llhs.toMtree[m.Term]
                val mop = lop.toMtree[m.Term.Name]
                val mtargs = ltargs.toMtrees[m.Type]
                val margs = largs.toMtrees[m.Term]
                m.Term.ApplyInfix(mlhs, mop, mtargs, margs)

              case l.TermApplyType(lfun, ltargs) =>
                val mfun = lfun.toMtree[m.Term]
                val mtargs = ltargs.toMtrees[m.Type]
                m.Term.ApplyType(mfun, mtargs)

              case l.TermAssign(llhs, lrhs) =>
                val mlhs = llhs.toMtree[m.Term.Ref]
                val mrhs = lrhs.toMtree[m.Term]
                m.Term.Assign(mlhs, mrhs)

              case l.TermReturn(lexpr) =>
                val mexpr = lexpr.toMtree[m.Term]
                m.Term.Return(mexpr)

              case l.TermThrow(lexpr) =>
                val mexpr = lexpr.toMtree[m.Term]
                m.Term.Throw(mexpr)

              case l.TermAscribe(lexpr, ldecltpe) =>
                val mexpr = lexpr.toMtree[m.Term]
                val mdecltpe = ldecltpe.toMtree[m.Type]
                m.Term.Ascribe(mexpr, mdecltpe)

              case l.TermAnnotate(lexpr, lannots) =>
                val mexpr = lexpr.toMtree[m.Term]
                val mannots = lannots.toMtrees[m.Mod.Annot]
                m.Term.Annotate(mexpr, mannots)

              case l.TermTuple(lelements) =>
                val melements = lelements.toMtrees[m.Term]
                m.Term.Tuple(melements)

              case l.TermBlock(lstats) =>
                val mstats = lstats.toMtrees[m.Stat]
                m.Term.Block(mstats)

              case l.TermIf(lcond, lthen, lelse) =>
                val mcond = lcond.toMtree[m.Term]
                val mthen = lthen.toMtree[m.Term]
                val melse = lelse.toMtree[m.Term]
                m.Term.If(mcond, mthen, melse)

              case l.TermMatch(lscrut, lcases) =>
                val mscrut = lscrut.toMtree[m.Term]
                val mcases = lcases.toMtrees[m.Case]
                m.Term.Match(mscrut, mcases)

              case l.TermTryWithCases(lexpr, lcatches, lfinally) =>
                val mexpr = lexpr.toMtree[m.Term]
                val mcatches = lcatches.toMtrees[m.Case]
                val mfinally = lfinally.toMtreeopt[m.Term]
                m.Term.Try(mexpr, mcatches, mfinally)

              case l.TermFunction(lparams, lbody) =>
                val mparams = lparams.toMtrees[m.Term.Param]
                val mbody = lbody.toMtree[m.Term]
                m.Term.Function(mparams, mbody)

              case l.TermPartialFunction(lcases) =>
                val mcases = lcases.toMtrees[m.Case]
                m.Term.PartialFunction(mcases)

              case l.TermWhile(lexpr, lbody) =>
                val mexpr = lexpr.toMtree[m.Term]
                val mbody = lbody.toMtree[m.Term]
                m.Term.While(mexpr, mbody)

              case l.TermDo(lbody, lexpr) =>
                val mbody = lbody.toMtree[m.Term]
                val mexpr = lexpr.toMtree[m.Term]
                m.Term.Do(mbody, mexpr)

              case l.TermPlaceholder() =>
                m.Term.Placeholder()

              case l.TermNew(ltempl) =>
                val mtempl = ltempl.toMtree[m.Template]
                if (!ltempl.stats.isDefined && mtempl.early.isEmpty)
                  m.Term.New(mtempl.inits.head)
                else
                  m.Term.NewAnonymous(mtempl)

              case l.TermEta(lexpr) =>
                val mexpr = lexpr.toMtree[m.Term]
                m.Term.Eta(mexpr)

              case l.TermArg.Named(lname, lrhs) =>
                val mname = lname.toMtree[m.Term]
                val mrhs = lrhs.toMtree[m.Term]
                m.Term.Assign(mname, mrhs)

              case l.TermArg.Repeated(lident) =>
                val mterm = lident.toMtree[m.Term]
                m.Term.Repeated(mterm)

              case l.TermParamDef(lmods, lname, ltpt, ldefault) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mname = lname.toMtree[m.Name]
                val mtpt = ltpt.toMtreeopt[m.Type]
                val mdefault = ldefault.toMtreeopt[m.Term]
                m.Term.Param(mmods, mname, mtpt, mdefault)

              // ============ TYPES ============

              case l.TypeName(lvalue) =>
                m.Type.Name(lvalue)

              case l.TypeIdent(lname) =>
                lname.toMtree[m.Type.Name]

              case l.TypeSelect(lqual, lname) =>
                val mqual = lqual.toMtree[m.Term.Ref]
                val mname = lname.toMtree[m.Type.Name]
                m.Type.Select(mqual, mname)

              case l.TypeProject(lqual, lname) =>
                val mqual = lqual.toMtree[m.Type]
                val mname = lname.toMtree[m.Type.Name]
                m.Type.Project(mqual, mname)

              case l.TypeSingleton(lref) =>
                val mref = lref.toMtree[m.Term.Ref]
                m.Type.Singleton(mref)

              case l.TypeArgByName(ltpe) =>
                val mtpe = ltpe.toMtree[m.Type]
                m.Type.ByName(mtpe)

              case l.TypeArgRepeated(ltpe) =>
                val mtpe = ltpe.toMtree[m.Type]
                m.Type.Repeated(mtpe)

              case l.TypeApply(ltpt, largs) =>
                val mtpt = ltpt.toMtree[m.Type]
                val margs = largs.toMtrees[m.Type]
                m.Type.Apply(mtpt, margs)

              case l.TypeApplyInfix(llhs, lop, lrhs) =>
                val mlhs = llhs.toMtree[m.Type]
                val mop = lop.toMtree[m.Type.Name]
                val mrhs = lrhs.toMtree[m.Type]
                m.Type.ApplyInfix(mlhs, mop, mrhs)

              case l.TypeFunction(lparams, lres) =>
                val mparams = lparams.toMtrees[m.Type]
                val mres = lres.toMtree[m.Type]
                m.Type.Function(mparams, mres)

              case l.TypeTuple(lelements) =>
                val melements = lelements.toMtrees[m.Type]
                m.Type.Tuple(melements)

              case l.TypeWith(llhs, lrhs) =>
                val mlhs = llhs.toMtree[m.Type]
                val mrhs = lrhs.toMtree[m.Type]
                m.Type.With(mlhs, mrhs)

              case l.TypeRefine(ltpe, lstats) =>
                val mtpe = ltpe.toMtreeopt[m.Type]
                val mstats = lstats.toMtrees[m.Stat]
                m.Type.Refine(mtpe, mstats)

              case l.TypeExistential(ltpe, lstats) =>
                val mtpe = ltpe.toMtree[m.Type]
                val mstats = lstats.toMtrees[m.Stat]
                m.Type.Existential(mtpe, mstats)

              case l.TypeAnnotate(ltpe, lannots) =>
                val mtpe = ltpe.toMtree[m.Type]
                val mannots = lannots.toMtrees[m.Mod.Annot]
                m.Type.Annotate(mtpe, mannots)

              case l.TypeBounds(llo, lhi) =>
                val mlo = llo.toMtreeopt[m.Type]
                val mhi = lhi.toMtreeopt[m.Type]
                m.Type.Bounds(mlo, mhi)

              case l.TypeParamDef(lmods, lname, ltparams, ltbounds, lvbounds, lcbounds) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mname = lname.toMtree[m.Name]
                val mtparams = ltparams.toMtrees[m.Type.Param]
                val mtbounds = ltbounds.toMtree[m.Type.Bounds]
                val mvbounds = lvbounds.toMtrees[m.Type]
                val mcbounds = lcbounds.toMtrees[m.Type]
                m.Type.Param(mmods, mname, mtparams, mtbounds, mvbounds, mcbounds)

              // ============ PATTERNS ============

              case l.PatVarTerm(lname) =>
                val mname = lname.toMtree[m.Term.Name]
                m.Pat.Var(mname)

              case l.PatVarType(lname) =>
                val mname = lname.toMtree[m.Type.Name]
                m.Type.Var(mname)

              case l.PatWildcard() =>
                m.Pat.Wildcard()

              case l.PatBind(llhs, lrhs) =>
                val mlhs = llhs.toMtree[m.Pat.Var]
                val mrhs = lrhs.toMtree[m.Pat]
                // NOTE: This pattern match goes against the rules of ToMtree.
                // Typically, the idea is that all non-trivial logic goes into extractors in LogicalTree.
                // However, in this case, that'd be too complicated engineering-wise, so I make an exception.
                mrhs match {
                  case m.Pat.Wildcard() => mlhs
                  case mrhs => m.Pat.Bind(mlhs, mrhs)
                }

              case l.PatAlternative(llhs, lrhs) =>
                val mllhs = llhs.toMtree[m.Pat]
                val mlrhs = lrhs.toMtree[m.Pat]
                m.Pat.Alternative(mllhs, mlrhs)

              case l.PatTuple(lelements) =>
                val melements = lelements.toMtrees[m.Pat]
                m.Pat.Tuple(melements)

              case l.PatExtract(lref, ltargs, largs) =>
                val mref = lref.toMtree[m.Term.Ref]
                val margs = largs.toMtrees[m.Pat]
                m.Pat.Extract(mref, margs)

              case l.PatInterpolate(lprefix, lparts, largs) =>
                val mprefix = lprefix.toMtree[m.Term.Name]
                val mparts = lparts.toMtrees[m.Lit]
                val margs = largs.toMtrees[m.Pat]
                m.Pat.Interpolate(mprefix, mparts, margs)

              case l.PatTyped(llhs, lrhs) =>
                val mlrhs = llhs.toMtree[m.Pat]
                val mrhs = lrhs.toMtree[m.Type]
                m.Pat.Typed(mlrhs, mrhs)

              case l.PatArgSeqWildcard() =>
                m.Pat.SeqWildcard()

              case l.PatTypeWildcard() =>
                m.Pat.Wildcard()
                m.Type.Placeholder(m.Type.Bounds(None, None))

              case l.PatTypeAnnotate(ltpe, lannots) =>
                val mtpe = ltpe.toMtree[m.Type]
                val mannots = lannots.toMtrees[m.Mod.Annot]
                m.Type.Annotate(mtpe, mannots)

              case l.PatTypeApply(ltpt, largs) =>
                val mtpt = ltpt.toMtree[m.Type]
                val margs = largs.toMtrees[m.Type]
                m.Type.Apply(mtpt, margs)

              case l.PatTypeWith(llhs, lrhs) =>
                val mlhs = llhs.toMtree[m.Type]
                val mrhs = lrhs.toMtree[m.Type]
                m.Type.With(mlhs, mrhs)

              // ============ LITERALS ============
              case l.Literal(null) =>
                m.Lit.Null()
              case l.Literal(value: Int) =>
                m.Lit.Int(value)
              case l.Literal(value: Double) =>
                m.Lit.Double(value)
              case l.Literal(value: Float) =>
                m.Lit.Float(value)
              case l.Literal(value: Byte) =>
                m.Lit.Byte(value)
              case l.Literal(value: Short) =>
                m.Lit.Short(value)
              case l.Literal(value: Char) =>
                m.Lit.Char(value)
              case l.Literal(value: Long) =>
                m.Lit.Long(value)
              case l.Literal(value: Boolean) =>
                m.Lit.Boolean(value)
              case l.Literal(value: Unit) =>
                m.Lit.Unit()
              case l.Literal(value: String) =>
                m.Lit.String(value)
              case l.Literal(value: scala.Symbol) =>
                m.Lit.Symbol(value)

              // ============ DECLS ============
              case l.DeclVal(lmods, lpats, ldecltpe) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mpats = lpats.toMtrees[m.Pat.Var]
                val mdecltpe = ldecltpe.toMtree[m.Type]
                m.Decl.Val(mmods, mpats, mdecltpe)

              case l.DeclVar(lmods, lpats, ldecltpe) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mpats = lpats.toMtrees[m.Pat.Var]
                val mdecltpe = ldecltpe.toMtree[m.Type]
                m.Decl.Var(mmods, mpats, mdecltpe)

              case l.AbstractDefDef(lmods, lname, ltparams, lparamss, ltpt) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mname = lname.toMtree[m.Term.Name]
                val mtparams = ltparams.toMtrees[m.Type.Param]
                val mparamss = lparamss.toMtreess[m.Term.Param]
                val mtpt = ltpt.toMtree[m.Type]
                m.Decl.Def(mmods, mname, mtparams, mparamss, mtpt)

              case l.AbstractTypeDef(lmods, lname, ltparams, lbounds) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mname = lname.toMtree[m.Type.Name]
                val mtparams = ltparams.toMtrees[m.Type.Param]
                val mbounds = lbounds.toMtree[m.Type.Bounds]
                m.Decl.Type(mmods, mname, mtparams, mbounds)

              // ============ DEFNS ============

              case l.DefnVal(lmods, lpats, ltpt, lrhs) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mpats = lpats.toMtrees[m.Pat]
                val mtpt = ltpt.toMtreeopt[m.Type]
                val mrhs = lrhs.toMtree[m.Term]
                m.Defn.Val(mmods, mpats, mtpt, mrhs)

              case l.DefnVar(lmods, lpats, ltpt, lrhs) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mpats = lpats.toMtrees[m.Pat]
                val mtpt = ltpt.toMtreeopt[m.Type]
                val mrhs = lrhs.toMtreeopt[m.Term]
                m.Defn.Var(mmods, mpats, mtpt, mrhs)

              case l.DefDef(lmods, lname, ltparams, lparamss, ltpt, lrhs) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mname = lname.toMtree[m.Term.Name]
                val mtparams = ltparams.toMtrees[m.Type.Param]
                val mparamss = lparamss.toMtreess[m.Term.Param]
                val mtpt = ltpt.toMtreeopt[m.Type]
                val mrhs = lrhs.toMtree[m.Term]
                m.Defn.Def(mmods, mname, mtparams, mparamss, mtpt, mrhs)

              case l.MacroDef(lmods, lname, ltparams, lparamss, ltpt, lrhs) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mname = lname.toMtree[m.Term.Name]
                val mtparams = ltparams.toMtrees[m.Type.Param]
                val mparamss = lparamss.toMtreess[m.Term.Param]
                val mtpt = ltpt.toMtreeopt[m.Type]
                val mrhs = lrhs.toMtree[m.Term]
                m.Defn.Macro(mmods, mname, mtparams, mparamss, mtpt, mrhs)

              case l.TypeDef(lmods, lname, ltparams, lbody) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mname = lname.toMtree[m.Type.Name]
                val mtparams = ltparams.toMtrees[m.Type.Param]
                val mbody = lbody.toMtree[m.Type]
                m.Defn.Type(mmods, mname, mtparams, mbody)

              case l.ClassDef(lmods, lname, ltparams, lctor, limpl) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mname = lname.toMtree[m.Type.Name]
                val mtparams = ltparams.toMtrees[m.Type.Param]
                val mctor = lctor.toMtree[m.Ctor.Primary]
                val mimpl = limpl.toMtree[m.Template]
                m.Defn.Class(mmods, mname, mtparams, mctor, mimpl)

              case l.TraitDef(lmods, lname, ltparams, lctor, limpl) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mname = lname.toMtree[m.Type.Name]
                val mtparams = ltparams.toMtrees[m.Type.Param]
                val mctor = {
                  // TODO: This conditional expression is non-idiomatic.
                  // We should strive to move all non-trivial logic to LogicalTrees.
                  if (lctor == g.EmptyTree) m.Ctor.Primary(Nil, m.Name(""), Nil)
                  else lctor.toMtree[m.Ctor.Primary]
                }
                val mimpl = limpl.toMtree[m.Template]
                m.Defn.Trait(mmods, mname, mtparams, mctor, mimpl)

              case l.ObjectDef(lmods, lname, limpl) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mname = lname.toMtree[m.Term.Name]
                val mimpl = limpl.toMtree[m.Template]
                m.Defn.Object(mmods, mname, mimpl)

              // ============ PKGS ============

              case l.PackageDef(lref, lstats) =>
                val mref = lref.toMtree[m.Term.Ref]
                val mstats = lstats.toMtrees[m.Stat]
                m.Pkg(mref, mstats)

              case l.PackageObjectDef(lmods, lname, ltempl) =>
                val mmods = lmods.toMtrees[m.Mod]
                val mname = lname.toMtree[m.Term.Name]
                val mtempl = ltempl.toMtree[m.Template]
                m.Pkg.Object(mmods, mname, mtempl)

              // ============ CTORS ============

              case l.PrimaryCtorDef(lmods, lname, lparamss) =>
                val mmods = lmods.toMtrees[m.Mod]
                // TODO: fixme https://github.com/xeno-by/scalameta/blob/7b9632ff889268a1c8c7c71432998e553146eab0/scalameta/parsers/src/main/scala/scala/meta/internal/parsers/ScalametaParser.scala#L3096
                // val mname = lname.toMtree[m.Ctor.Name]
                val mname = m.Name("")
                val mparamss = lparamss.toMtreess[m.Term.Param]
                m.Ctor.Primary(mmods, mname, mparamss)

              case l.SecondaryCtorDef(lmods, lname, lparamss, lbody) =>
                def loop(mbody: m.Term.Apply): List[List[m.Term]] = mbody match {
                  case m.Term.Apply(mapply: m.Term.Apply, args) => loop(mapply) ++ List(args)
                  case m.Term.Apply(_,                    args) => List(args)
                }
                val mmods = lmods.toMtrees[m.Mod]
                val mname = m.Name("")
                val mparamss = lparamss.toMtreess[m.Term.Param]
                val margss = loop(lbody.toMtree[m.Term.Apply])
                m.Ctor.Secondary(mmods, mname, mparamss, m.Init(
                  m.Type.Singleton(m.Term.This(m.Name(""))), m.Name(""), margss
                ), Nil)

              case l.CtorName(lvalue) =>
                if (lvalue == "this")
                  m.Term.This(m.Name(""))
                else
                  m.Name(lvalue)

              case l.CtorIdent(lname) =>
                lname.toMtree[m.Name]

              // ============ TEMPLATES ============

              case l.Template(learly, lparents, lself, lstats) =>
                val mearly = learly.toMtrees[m.Stat]
                val mparents = lparents.toMtrees[m.Init].map(_.copy(name = m.Name("")))
                val mself = lself.toMtree[m.Self]
                val mstats = lstats.map(_.toMtrees[m.Stat])
                m.Template(mearly, mparents, mself, mstats.getOrElse(Nil))

              case l.Parent(ltpt, lctor, largss) =>
                val mtpt = ltpt.toMtree[m.Type]
                val mctor = lctor.toMtree[m.Name]
                val margss = largss.toMtreess[m.Term]
                m.Init(mtpt, mctor, margss)

              case l.Self(lname, ltpt) =>
                val mname = lname.toMtree[m.Name]
                val mtpt = if (ltpt.nonEmpty) Some(ltpt.toMtree[m.Type]) else None
                m.Self(mname, mtpt)

              // ============ MODIFIERS ============

              case l.Annotation(lapply) =>
                // scala.reflect uses Term.New here, but we need only its parent
                val m.Term.New(init) = lapply.toMtree[m.Term.New]
                m.Mod.Annot(init)

              case l.Private(lwithin) =>
                val mwithin = lwithin.toMtree[m.Ref]
                m.Mod.Private(mwithin)

              case l.Protected(lwithin) =>
                val mwithin = lwithin.toMtree[m.Ref]
                m.Mod.Protected(mwithin)

              case l.Implicit() =>
                m.Mod.Implicit()

              case l.Final() =>
                m.Mod.Final()

              case l.Sealed() =>
                m.Mod.Sealed()

              case l.Override() =>
                m.Mod.Override()

              case l.Case() =>
                m.Mod.Case()

              case l.Abstract() =>
                m.Mod.Abstract()

              case l.Covariant() =>
                m.Mod.Covariant()

              case l.Contravariant() =>
                m.Mod.Contravariant()

              case l.Lazy() =>
                m.Mod.Lazy()

              case l.ValParam() =>
                m.Mod.ValParam()

              case l.VarParam() =>
                m.Mod.VarParam()

              case l.Inline() =>
                m.Mod.Inline()

              // ============ ODDS & ENDS ============

              case l.Importer(lref, limportees) =>
                val mref = lref.toMtree[m.Term.Ref]
                val mimportees = limportees.toMtrees[m.Importee]
                m.Import(List(m.Importer(mref, mimportees)))

              case l.ImporteeWildcard() =>
                m.Importee.Wildcard()

              case l.ImporteeName(lname) =>
                val mname = lname.toMtree[m.Name.Indeterminate]
                m.Importee.Name(mname)

              case l.ImporteeRename(lname, lrename) =>
                val mname = lname.toMtree[m.Name.Indeterminate]
                val mrename = lrename.toMtree[m.Name.Indeterminate]
                m.Importee.Rename(mname, mrename)

              case l.ImporteeUnimport(lname) =>
                val mname = lname.toMtree[m.Name.Indeterminate]
                m.Importee.Unimport(mname)

              case l.CaseDef(lpat, lguard, lbody) =>
                val mpat = lpat.toMtree[m.Pat]
                val mguard = lguard.toMtreeopt[m.Term]
                val mbody = lbody.toMtree[m.Term]
                m.Case(mpat, mguard, mbody)

              case _ =>
                fail(s"unsupported tree ${g.showRaw(gtree)}")
            }
            mtree
          })
        }
      }

      implicit class RichTreeoptToMtreeopt(gtreeopt: Option[g.Tree]) {
        def toMtreeopt[T <: m.Tree: ClassTag]: Option[T] = gtreeopt.map(_.toMtree[T])
      }

      implicit class RichTreesToMtrees(gtrees: List[g.Tree]) {
        def toMtrees[T <: m.Tree: ClassTag]: List[T] = gtrees.map(_.toMtree[T])
      }

      implicit class RichTreessToMtreess(gtreess: List[List[g.Tree]]) {
        def toMtreess[T <: m.Tree: ClassTag]: List[List[T]] = gtreess.map(_.toMtrees[T])
      }

      var backtrace = List[g.Tree]()
      def wrap[T <: m.Tree: ClassTag](gtree0: g.Tree, converter: (g.Tree, g.Tree) => m.Tree): T = {
        val isDuplicate = backtrace.nonEmpty && backtrace.head == gtree0
        if (!isDuplicate) backtrace = gtree0 +: backtrace
        try {
          val (gtree, gexpansion) = (gtree0, g.EmptyTree)
          val undesugaredTree = l.UndoDesugaring.unapply(gtree).getOrElse(gtree)
          val convertedTree = converter(undesugaredTree, gexpansion)
          val maybeTypecheckedMtree = convertedTree
          val maybeIndexedMtree = maybeTypecheckedMtree
          if (classTag[T].runtimeClass.isAssignableFrom(maybeIndexedMtree.getClass)) {
            maybeIndexedMtree.asInstanceOf[T]
          } else {
            var expected = classTag[T].runtimeClass.getName
            expected = expected.stripPrefix("scala.meta.internal.ast.").stripPrefix("scala.meta.")
            expected = expected.stripSuffix("$Impl")
            expected = expected.replace("$", ".")
            val actual = maybeIndexedMtree.productPrefix
            val summary = s"expected = $expected, actual = $actual"
            val details = s"${g.showRaw(gtree)}$EOL${maybeIndexedMtree.structure}"
            fail(s"unexpected result: $summary$EOL$details")
          }
        } catch {
          case ex: ConvertException =>
            throw ex
          case ex: Exception =>
            fail(s"unexpected error (scroll down the stacktrace to see the cause):", Some(ex))
          case ex: NotImplementedError =>
            fail(s"unexpected error (scroll down the stacktrace to see the cause):", Some(ex))
        } finally {
          if (!isDuplicate) backtrace = backtrace.tail
        }
      }

      def fail(diagnostics: String, ex: Option[Throwable] = None): Nothing = {
        val s_backtrace = backtrace
          .map(gtree => {
            val prefix = gtree.productPrefix
            val details = gtree.toString()
            s"($prefix) $details"
          })
          .mkString(EOL)
        throw new ConvertException(backtrace.head, s"$diagnostics$EOL$s_backtrace", ex)
      }

      def apply[T <: m.Tree: ClassTag](gtree: g.Tree): T = {
        val mtree = wrap[T](gtree, (gtree, gexpansion) => {
          gtree match {
            case g.PackageDef(g.Ident(g.nme.EMPTY_PACKAGE_NAME), gstats) =>
              val mstats = gstats.toMtrees[m.Stat]
              m.Source(mstats)
            case g.PackageDef(_, _) if classTag[T].runtimeClass == classOf[m.Source] =>
              val mstats = List(gtree.toMtree[m.Pkg])
              m.Source(mstats)
            case l.PackageObjectDef(_, _, _) =>
              gtree.toMtree[m.Pkg.Object]
            case g.PackageDef(_, _) =>
              gtree.toMtree[m.Pkg]
            case _ =>
              gtree.toMtree[T]
          }
        })
        mtree
      }
    }
    toMtree.apply[T](gtree)
  }
}
