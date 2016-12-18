/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

trait TreeTransformer extends inox.ast.TreeTransformer { self =>
  val s: Trees
  val t: Trees

  override lazy val deconstructor: TreeDeconstructor { val s: self.s.type; val t: self.t.type } = {
    s.getDeconstructor(t).asInstanceOf[TreeDeconstructor { val s: self.s.type; val t: self.t.type }]
  }

  def transform(pat: s.Pattern): t.Pattern = {
    val (vs, es, tps, pats, builder) = deconstructor.deconstruct(pat)

    var changed = false
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
      builder(newVs, newEs, newTps, newPats).copiedFrom(pat)
    } else {
      pat.asInstanceOf[t.Pattern]
    }
  }
}
