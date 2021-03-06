import scala.annotation.StaticAnnotation
import scala.meta._

class companion extends StaticAnnotation {

  inline def apply(stats: Any): Any = meta {
    def extractClass(classDefn: Defn.Class): Stat = {
      val q"""
        ..$mods class $tname[..$tparams] ..$ctorMods (...$paramss) extends { ..$earlyStats } with ..$ctorcalls {
          $selfParam =>
          ..$stats
        }
      """ = classDefn
      q"""
        ..$mods class $tname[..$tparams] ..$ctorMods (...$paramss) extends { ..$earlyStats } with ..$ctorcalls {
          $selfParam =>
          ..$stats
        }
      """
    }

    def extractObj(objDefn: Defn.Object): Stat = {
      val q"""
        ..$mods object $tname extends { ..$earlyStats } with ..$ctorcalls {
          $selfParam =>
          ..$stats
        }
      """ = objDefn
      q"""
        ..$mods object $tname extends { ..$earlyStats } with ..$ctorcalls {
          $selfParam =>
          ..$stats
        }
      """
    }

    stats match {
      case Term.Block(Seq(classDefn: Defn.Class, objDefn: Defn.Object)) =>
        Term.Block(List(extractClass(classDefn), extractObj(objDefn)))
      case classDefn: Defn.Class => extractClass(classDefn)
    }
  }

}
