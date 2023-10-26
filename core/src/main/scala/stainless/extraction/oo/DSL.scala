package stainless
package extraction
package oo

import scala.language.implicitConversions

trait DSL extends ast.DSL {
  protected val trees: Trees
  import trees._

  case class K(id: Identifier) {
    def apply(tps: Type*): ClassType = ClassType(id, tps)
  }
  final class MatchDSL(var cases: Seq[MatchCase], var locked: Boolean)
  final class CaseDSL(pat: PatternDSL)(using mdsl: MatchDSL) {
    def if_(expr: Expr)(body: => Expr): Unit = {
      ???
    }
    def apply(body: => Expr): Unit = {
      ???
    }
  }

  trait PatternDSL {
    def compiled: Pattern
  }
  trait UnboundPatternDSL {
    def compiled(vd: ValDef): Pattern
  }

  object unused extends PatternDSL {
    override def compiled: Pattern = WildcardPattern(None)
  }

  case class KP2(ct: ClassType, sub: Seq[PatternDSL], dummy: Unit) extends PatternDSL {
    override def compiled: Pattern = ClassPattern(None, ct, sub.map(_.compiled))
  }
  object KP2 {
    def apply(ct: ClassType)(sub: PatternDSL*): KP2 = KP2(ct, sub.toSeq, ())
  }
  case class KP(sub: Seq[PatternDSL], dummy: Unit) extends UnboundPatternDSL {
    override def compiled(vd: ValDef): Pattern = {
      val ct = vd.tpe match {
        case ct: ClassType => ct
        case _ => throw IllegalPatternDSLUsage(s"KP(...) pattern expects a ClassType variable but was given ${vd.tpe}")
      }
      ClassPattern(Some(vd), ct, sub.map(_.compiled))
    }
  }

  object KP {
    def apply(sub: PatternDSL*): KP = new KP(sub.toSeq, ())
  }
  case class BoundPattern(vd: ValDef, pat: UnboundPatternDSL) extends PatternDSL {
    override def compiled: Pattern = pat.compiled(vd)
  }
  case class WildcardDSL(vd: ValDef) extends PatternDSL {
    override def compiled: Pattern = WildcardPattern(Some(vd))
  }

  implicit def vd2wc(vd: ValDef): PatternDSL = WildcardDSL(vd)

  extension (vd: ValDef) {
    def @@(cc: UnboundPatternDSL): PatternDSL = BoundPattern(vd, cc)
  }

  extension (e: Expr) {
    def match_(body: MatchDSL ?=> Unit): MatchExpr = {
      val mdsl = MatchDSL(Seq.empty, locked = false)
      body(using mdsl)
      MatchExpr(e, mdsl.cases).copiedFrom(e)
    }
  }

//  def case_(pat: PatternDSL)(using mdsl: MatchDSL): CaseDSL = {
//    ???
//  }

  def case_(pat: PatternDSL)(body: Seq[ValDef] => Expr)(using mdsl: MatchDSL): Unit = {
    if (mdsl.locked) {
      throw IllegalPatternDSLUsage("Cannot use `case_` within another `case_` without introducing a new `match_`")
    }
    mdsl.locked = true
    val compiled = pat.compiled
    val expr = body(ordBinders(compiled))
    mdsl.locked = false
    mdsl.cases = mdsl.cases :+ MatchCase(pat.compiled, None, expr).copiedFrom(expr)
  }

  private def ordBinders(pat: Pattern): Seq[ValDef] =
    pat.binder.toSeq ++ pat.subPatterns.flatMap(_.binder)

  def playground(scrut: Expr, cls: Identifier): Unit = {
    // TODO: With guard
    scrut match_ {
      case_(("x" :: K(cls)()) @@ KP(("y" :: K(cls)()) @@ KP("z" :: K(cls)()))) {
        case Seq(x, y, z) =>
          scrut
      }
//      case_(("x" :: K(cls)()) @@ KP(("y" :: K(cls)()) @@ KP("z" :: K(cls)()))).if_(scrut).apply({
//        scrut
//      })
      /*
      case_() what {
        scrut
      }*/
    }

  }

  case class IllegalPatternDSLUsage(msg: String) extends Exception(msg)
}
