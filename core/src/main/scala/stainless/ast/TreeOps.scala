/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

trait TreeOps extends inox.ast.TreeOps { self: Trees =>

  trait TreeTraverser extends super.TreeTraverser {
    override def traverse(e: Expr): Unit = e match {
      case MatchExpr(scrut, cases) =>
        traverse(scrut)
        cases.foreach { case MatchCase(pat, optGuard, rhs) =>
          traverse(pat)
          optGuard.foreach(traverse)
          traverse(rhs)
        }

      case _ => super.traverse(e)
    }

    def traverse(pat: Pattern): Unit = {
      val (ids, vs, es, tps, pats, _) = deconstructor.deconstruct(pat)
      ids.foreach(traverse)
      vs.foreach(v => traverse(v.toVal))
      es.foreach(traverse)
      tps.foreach(traverse)
      pats.foreach(traverse)
    }
  }
}

trait TreeTransformer extends inox.ast.TreeTransformer { self =>
  val s: Trees
  val t: Trees

  override lazy val deconstructor: TreeDeconstructor { val s: self.s.type; val t: self.t.type } = {
    s.getDeconstructor(t).asInstanceOf[TreeDeconstructor { val s: self.s.type; val t: self.t.type }]
  }

  override def transform(e: s.Expr): t.Expr = e match {
    case s.MatchExpr(scrut, cases) =>
      val newScrut = transform(scrut)

      var changed = false
      val newCases = for (cse @ s.MatchCase(pat, guard, rhs) <- cases) yield {
        val newPat = transform(pat)
        val newGuard = guard.map(transform)
        val newRhs = transform(rhs)

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

    case _ => super.transform(e)
  }

  def transform(pat: s.Pattern): t.Pattern = {
    val (ids, vs, es, tps, pats, builder) = deconstructor.deconstruct(pat)
    var changed = false

    val newIds = for (id <- ids) yield {
      val newId = transform(id)
      if (id ne newId) changed = true
      newId
    }

    val newVs = for (v <- vs) yield {
      val vd = v.toVal
      val newVd = transform(vd)
      if (vd ne newVd) changed = true
      newVd.toVariable
    }

    val newEs = for (e <- es) yield {
      val newE = transform(e)
      if (e ne newE) changed = true
      newE
    }

    val newTps = for (tp <- tps) yield {
      val newTp = transform(tp)
      if (tp ne newTp) changed = true
      newTp
    }

    val newPats = for (pat <- pats) yield {
      val newPat = transform(pat)
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
