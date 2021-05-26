/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait TransformerWithPC extends innerfuns.TransformerWithPC {
  val s: Trees
  val t: Trees

  override def transform(e: s.Expr, env: Env): t.Expr = e match {
    case s.LetVar(vd, v, b) =>
      t.LetVar(transform(vd, env), transform(v, env), transform(b, env withBinding (vd -> v))).copiedFrom(e)

    case s.While(cond, body, optInv, optWeakInv, flags) =>
      val bodyEnv1 = env withCond cond
      val bodyEnv2 = if (optInv.nonEmpty) bodyEnv1 withCond (optInv.get) else bodyEnv1
      val bodyEnv3 = if (optInv.nonEmpty) bodyEnv2 withCond (optWeakInv.get) else bodyEnv2
      t.While(
        transform(cond, env),
        transform(body, bodyEnv3),
        optInv.map(transform(_, env)),
        optWeakInv.map(transform(_, env)),
        flags.map(transform(_, env))
      ).copiedFrom(e)

    case _ => super.transform(e, env)
  }
}

