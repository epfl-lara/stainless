/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait TransformerWithPC extends innerfuns.TransformerWithPC {
  val s: Trees
  val t: Trees

  override def transform(e: s.Expr, env: Env): t.Expr = e match {
    case s.LetVar(vd, v, b) =>
      t.LetVar(transform(vd, env), transform(v, env), transform(b, env withBinding (vd -> v))).copiedFrom(e)

    case _ => super.transform(e, env)
  }
}

