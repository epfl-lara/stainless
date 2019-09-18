/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package innerfuns

trait TransformerWithPC extends transformers.TransformerWithPC {
  val s: Trees
  val t: Trees

  override def transform(e: s.Expr, env: Env): t.Expr = e match {
    case s.LetRec(defs, body) =>
      t.LetRec(
        defs map { case fd @ s.LocalFunDef(id, tparams, params, returnType, fullBody, flags) =>
          val (newEnv, newParams) = params.foldLeft((env, Seq.empty[t.ValDef])) {
            case ((env, newParams), vd) => (env withBound vd, newParams :+ transform(vd, env))
          }

          t.LocalFunDef(
            transform(id, env),
            tparams map (transform(_, env)),
            newParams,
            transform(returnType, newEnv),
            transform(fullBody, newEnv),
            flags map (transform(_, env))
          ).copiedFrom(fd)
        },
        transform(body, env)
      ).copiedFrom(e)

    case _ => super.transform(e, env)
  }
}
