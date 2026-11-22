/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package throwing

trait TransformerWithPC extends imperative.TransformerWithPC {
  val s: Trees
  val t: Trees

  override def transform(e: s.Expr, env: Env): t.Expr = e match {
    // The cases of a `try` match on the exception that is caught, which is not an expression of
    // the program: their binders are bound in a path where the exception is a fresh variable.
    case s.Try(body, cases, fin) =>
      val excType = symbols.lookup.get[s.ClassDef]("stainless.lang.Exception")
        .map(cd => s.ClassType(cd.id, Seq()))
        .getOrElse(s.AnyType())
      val exc = s.ValDef.fresh("exc", excType).copiedFrom(e)
      val caseEnv = env `withBound` exc
      t.Try(
        transform(body, env),
        cases.map { c =>
          val patternPath = symbols.conditionForPattern[Env](exc.toVariable, c.pattern, includeBinders = true)
          val guardEnv = caseEnv `merge` patternPath
          t.MatchCase(
            transform(c.pattern, caseEnv),
            c.optGuard.map(transform(_, guardEnv)),
            transform(c.rhs, guardEnv `withCond` c.optGuard.getOrElse(s.BooleanLiteral(true).copiedFrom(c)))
          ).copiedFrom(c)
        },
        fin.map(transform(_, env))
      ).copiedFrom(e)

    case _ => super.transform(e, env)
  }
}
