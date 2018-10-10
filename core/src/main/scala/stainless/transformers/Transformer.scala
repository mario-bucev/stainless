/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package transformers

trait Transformer extends inox.transformers.Transformer { self =>
  val s: ast.Trees
  val t: ast.Trees

  // required override to get access to the pattern deconstructor
  override lazy val deconstructor: ast.TreeDeconstructor { val s: self.s.type; val t: self.t.type } = {
    s.getDeconstructor(t).asInstanceOf[ast.TreeDeconstructor { val s: self.s.type; val t: self.t.type }]
  }

  override def transform(e: s.Expr, env: Env): t.Expr = e match {
    case s.MatchExpr(scrut, cases) =>
      val newScrut = transform(scrut, env)

      var changed = false
      val newCases = for (cse @ s.MatchCase(pat, guard, rhs) <- cases) yield {
        val newPat = transform(pat, env)
        val newGuard = guard.map(transform(_, env))
        val newRhs = transform(rhs, env)

        if ((pat ne newPat) || guard.exists(_ ne newGuard.get) || (rhs ne newRhs) || (s ne t)) {
          changed = true
          t.MatchCase(newPat, newGuard, newRhs).copiedFrom(cse)
        } else {
          cse.asInstanceOf[t.MatchCase]
        }
      }

      if ((scrut ne newScrut) || changed || (s ne t)) {
        t.MatchExpr(newScrut, newCases).copiedFrom(e)
      } else {
        e.asInstanceOf[t.Expr]
      }

    case _ => super.transform(e, env)
  }

  def transform(pat: s.Pattern, env: Env): t.Pattern = {
    val (ids, vs, es, tps, pats, builder) = deconstructor.deconstruct(pat)
    var changed = false

    val newIds = for (id <- ids) yield {
      val newId = transform(id, env)
      if (id ne newId) changed = true
      newId
    }

    val newVs = for (v <- vs) yield {
      val vd = v.toVal
      val newVd = transform(vd, env)
      if (vd ne newVd) changed = true
      newVd.toVariable
    }

    val newEs = for (e <- es) yield {
      val newE = transform(e, env)
      if (e ne newE) changed = true
      newE
    }

    val newTps = for (tp <- tps) yield {
      val newTp = transform(tp, env)
      if (tp ne newTp) changed = true
      newTp
    }

    val newPats = for (pat <- pats) yield {
      val newPat = transform(pat, env)
      if (pat ne newPat) changed = true
      newPat
    }

    if (changed || (s ne t)) {
      builder(newIds, newVs, newEs, newTps, newPats).copiedFrom(pat)
    } else {
      pat.asInstanceOf[t.Pattern]
    }
  }
}

trait DefinitionTransformer extends inox.transformers.DefinitionTransformer with Transformer

trait TreeTransformer extends DefinitionTransformer with inox.transformers.TreeTransformer {
  def transform(pat: s.Pattern): t.Pattern = super.transform(pat, ())
  override final def transform(pat: s.Pattern, env: Env): t.Pattern = transform(pat)
}