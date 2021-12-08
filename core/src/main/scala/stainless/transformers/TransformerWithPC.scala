/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package transformers

trait TransformerWithPC extends inox.transformers.TransformerWithPC with Transformer {
  val symbols: s.Symbols
  val pp: s.PathProvider[Env]
  given givenPP: pp.type = pp

  override def transform(e: s.Expr, env: Env): t.Expr = e match {
    case s.Ensuring(req @ s.Require(pre, body), l @ s.Lambda(Seq(vd), post)) =>
      t.Ensuring(
        t.Require(transform(pre, env), transform(body, env withCond pre)).copiedFrom(req),
        t.Lambda(Seq(transform(vd, env)), transform(post, env withCond pre withBinding (vd -> body))).copiedFrom(l)
      ).copiedFrom(e)

    case s.Ensuring(body, l @ s.Lambda(Seq(vd), post)) =>
      t.Ensuring(
        transform(body, env),
        t.Lambda(Seq(transform(vd, env)), transform(post, env withBinding (vd -> body))).copiedFrom(l)
      ).copiedFrom(e)

    case s.Require(pre, body) =>
      t.Require(transform(pre, env), transform(body, env withCond pre)).copiedFrom(e)

    case s.Assert(pred, err, body) =>
      t.Assert(transform(pred, env), err, transform(body, env withCond pred)).copiedFrom(e)

    case s.Passes(in, out, cases) =>
      t.Passes(transform(in, env), transform(out, env), transformCases(cases, in, env)).copiedFrom(e)

    case s.MatchExpr(scrut, cases) =>
      t.MatchExpr(transform(scrut, env), transformCases(cases, scrut, env)).copiedFrom(e)

    case _ => super.transform(e, env)
  }

  private def transformCases(cases: Seq[s.MatchCase], scrut: s.Expr, env: Env) = {
    var soFar = env

    cases map { c =>
      val spattern = transform(c.pattern, soFar)
      val patternPathPos = symbols.conditionForPattern[Env](scrut, c.pattern, includeBinders = true)
      val patternPathNeg = symbols.conditionForPattern[Env](scrut, c.pattern, includeBinders = false)

      val sguard = c.optGuard.map(transform(_, soFar merge patternPathPos))
      val guardOrTrue = c.optGuard.getOrElse(s.BooleanLiteral(true).copiedFrom(c))

      import s._ // necessary for implicit VariableConverter in replaceFromSymbols
      val guardMapped = s.exprOps.replaceFromSymbols(symbols.mapForPattern(scrut, c.pattern), guardOrTrue)

      val subPath = soFar merge (patternPathPos withCond guardOrTrue)
      soFar = soFar merge (patternPathNeg withCond guardMapped).negate

      t.MatchCase(spattern, sguard, transform(c.rhs, subPath)).copiedFrom(c)
    }
  }
}

