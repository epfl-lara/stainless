/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package transformers

import inox.transformers.TransformerOp

trait Transformer extends inox.transformers.Transformer { self =>
  val s: ast.Trees
  val t: ast.Trees

  // required override to get access to the pattern deconstructor
  override lazy val deconstructor: ast.TreeDeconstructor { val s: self.s.type; val t: self.t.type } = {
    s.getDeconstructor(t).asInstanceOf[ast.TreeDeconstructor { val s: self.s.type; val t: self.t.type }]
  }

  def transformCase(cse: s.MatchCase, env: Env): t.MatchCase = {
    val s.MatchCase(pat, guard, rhs) = cse
    val newPat = transform(pat, env)
    val newGuard = guard.map(transform(_, env))
    val newRhs = transform(rhs, env)
    t.MatchCase(newPat, newGuard, newRhs).copiedFrom(cse)
  }

  def transformCases(cases: Seq[s.MatchCase], env: Env): (Seq[t.MatchCase], Boolean) = {
    var changed = false
    val newCases = for (cse @ s.MatchCase(pat, guard, rhs) <- cases) yield {
      val newCase = transformCase(cse, env)

      if ((pat ne newCase.pattern) || guard.exists(_ ne newCase.optGuard.get) || (rhs ne newCase.rhs) || (s ne t)) {
        changed = true
        newCase
      } else {
        cse.asInstanceOf[t.MatchCase]
      }
    }
    (newCases, changed)
  }

  override def transform(e: s.Expr, env: Env): t.Expr = e match {
    case s.MatchExpr(scrut, cases) =>
      val newScrut = transform(scrut, env)
      val (newCases, changed) = transformCases(cases, env)

      if ((scrut ne newScrut) || changed || (s ne t)) {
        t.MatchExpr(newScrut, newCases).copiedFrom(e)
      } else {
        e.asInstanceOf[t.Expr]
      }

    case s.Passes(in, out, cases) =>
      val newIn = transform(in, env)
      val newOut = transform(out, env)

      val (newCases, changed) = transformCases(cases, env)

      if ((in ne newIn) || (out ne newOut) || changed || (s ne t)) {
        t.Passes(newIn, newOut, newCases).copiedFrom(e)
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

class ConcreteTreeTransformer(override val s: ast.Trees, override val t: ast.Trees) extends TreeTransformer

trait TransformerWithPatternOp extends Transformer {
  private[this] val op = new TransformerOp[s.Pattern, Env, t.Pattern](transform(_, _), super.transform(_, _))

  protected val patternOp: (s.Pattern, Env, TransformerOp[s.Pattern, Env, t.Pattern]) => t.Pattern

  override def transform(pat: s.Pattern, env: Env): t.Pattern = patternOp(pat, env, op)
}
