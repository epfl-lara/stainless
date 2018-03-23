/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package transformers

trait SimplifierWithPC extends TransformerWithPC with inox.transformers.SimplifierWithPC {
  import trees._
  import symbols._
  def pp = implicitly[PathProvider[CNFPath]]

  override protected def simplify(e: Expr, path: CNFPath): (Expr, Boolean) = e match {
    case Assert(pred, oerr, body) => simplify(pred, path) match {
      case (BooleanLiteral(true), true) => simplify(body, path)
      case (BooleanLiteral(false), true) =>
        val (rb, _) = simplify(body, path)
        (Assert(BooleanLiteral(false).copiedFrom(e), oerr, rb).copiedFrom(e), opts.assumeChecked)
      case (rp, _) =>
        val (rb, _) = simplify(body, path withCond rp)
        (Assert(rp, oerr, rb).copiedFrom(e), opts.assumeChecked)
    }

    case MatchExpr(scrut, cases) =>
      val (rs, ps) = simplify(scrut, path)
      val (_, _, purity, newCases) = cases.foldLeft((path, false, ps, Seq[MatchCase]())) {
        case (p @ (_, true, _, _), _) => p
        case ((soFar, _, purity, newCases), MatchCase(pattern, guard, rhs)) =>
          simplify(conditionForPattern[Path](rs, pattern, includeBinders = false).fullClause, soFar) match {
            case (BooleanLiteral(false), true) => (soFar, false, purity, newCases)
            case (rc, pc) =>
              val path = conditionForPattern[CNFPath](rs, pattern, includeBinders = true)
              val (rg, pg) = guard.map(simplify(_, soFar merge path)).getOrElse((BooleanLiteral(true), true))
              (and(rc, rg), pc && pg) match {
                case (BooleanLiteral(false), true) => (soFar, false, purity, newCases)
                case (BooleanLiteral(true), true) =>
                  // We know path withCond rg is true here but we need the binders
                  val (rr, pr) = simplify(rhs, soFar merge path)
                  (soFar, true, purity && pr, newCases :+ MatchCase(pattern, None, rr))

                case (_, _) =>
                  val (rr, pr) = simplify(rhs, soFar merge (path withCond rg))
                  val newGuard = if (rg == BooleanLiteral(true)) None else Some(rg)
                  (
                    soFar merge (path withCond rg).negate,
                    false,
                    purity && pc && pg && pr,
                    newCases :+ MatchCase(pattern, newGuard, rr)
                  )
              }
          }
      }
      (MatchExpr(rs, newCases), purity)

    case _ => super.simplify(e, path)
  }
}
