/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package transformers

trait TransformerWithPC extends inox.transformers.TransformerWithPC {
  val trees: ast.Trees
  import trees._
  import symbols._

  implicit val pp: PathProvider[Env]

  override protected def rec(e: Expr, env: Env): Expr = e match {
    case Ensuring(req @ Require(pre, body), l @ Lambda(Seq(vd), post)) =>
      val spre = rec(pre, env)
      val sbody = rec(body, env withCond spre)
      val spost = rec(post, env withCond spre withBinding (vd -> sbody))
      Ensuring(
        Require(spre, sbody).copiedFrom(req),
        Lambda(Seq(vd), spost).copiedFrom(l)
      ).copiedFrom(e)

    case Ensuring(body, l @ Lambda(Seq(vd), post)) =>
      val sbody = rec(body, env)
      val spost = rec(post, env withBinding (vd -> sbody))
      Ensuring(sbody, Lambda(Seq(vd), spost).copiedFrom(l)).copiedFrom(e)

    case Require(pre, body) =>
      val spre = rec(pre, env)
      val sbody = rec(body, env withCond spre)
      Require(spre, sbody).copiedFrom(e)

    case Assert(pred, err, body) =>
      val spred = rec(pred, env)
      val sbody = rec(body, env withCond spred)
      Assert(spred, err, sbody).copiedFrom(e)

    case Dontcheck(body) => body

    case MatchExpr(scrut, cases) =>
      val rs = rec(scrut, env)

      var soFar = env

      MatchExpr(rs, cases.map { c =>
        val patternPathPos = conditionForPattern[Env](rs, c.pattern, includeBinders = true)
        val patternPathNeg = conditionForPattern[Env](rs, c.pattern, includeBinders = false)

        val map = mapForPattern(rs, c.pattern)
        val sguard = c.optGuard.map(rec(_, soFar))
        val guardOrTrue = sguard.getOrElse(BooleanLiteral(true))
        val guardMapped = exprOps.replaceFromSymbols(map, guardOrTrue)

        val subPath = soFar merge (patternPathPos withCond guardOrTrue)
        soFar = soFar merge (patternPathNeg withCond guardMapped).negate

        MatchCase(c.pattern, sguard, rec(c.rhs, subPath)).copiedFrom(c)
      }).copiedFrom(e)

    case _ => super.rec(e, env)
  }
}
