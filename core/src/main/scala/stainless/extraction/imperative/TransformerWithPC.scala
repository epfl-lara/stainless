/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait TransformerWithPC extends stainless.transformers.TransformerWithPC {
  override val trees: Trees
  import trees._

  override protected def rec(e: Expr, env: Env): Expr = e match {
    case LetVar(vd, v, b) =>
      val sv = rec(v, env)
      val sb = rec(v, env withBinding vd -> sv)
      LetVar(vd, sv, sb).copiedFrom(e)

    case _ => super.rec(e, env)
  }
}

