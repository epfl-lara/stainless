/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package transformers

trait SimplifierWithPC extends Transformer with inox.transformers.SimplifierWithPC {
  val trees: ast.Trees
  import trees._
  import symbols.{given, _}

  val pp: PathProvider[Env]
  given givenPP: pp.type = pp

  override protected def simplify(e: Expr, path: Env): (Expr, Boolean) = e match {
    case Let(vd, a @ Annotated(ADTSelector(v: Variable, _), flags), b) if flags.contains(DropVCs) =>
      simplify(exprOps.replaceFromSymbols(Map(vd -> a), b), path)

    case Let(vd, cs @ ADTSelector(v: Variable, _), b) =>
      simplify(exprOps.replaceFromSymbols(Map(vd -> cs), b), path)

    case Assert(pred, oerr, body) => simplify(pred, path) match {
      case (BooleanLiteral(true), true) => simplify(body, path)
      case (BooleanLiteral(false), true) =>
        val (rb, p) = simplify(body, path)
        (
          Assert(BooleanLiteral(false).copiedFrom(e), oerr, rb).copiedFrom(e),
          opts.assumeChecked && p
        )
      case (rp, _) =>
        val (rb, p) = simplify(body, path withCond rp)
        (Assert(rp, oerr, rb).copiedFrom(e), opts.assumeChecked && p)
    }

    case Require(pred, body) => simplify(pred, path) match {
      case (BooleanLiteral(true), true) => simplify(body, path)
      case (rp, _) =>
        val (rb, p) = simplify(body, path withCond rp)
        (Require(rp, rb).copiedFrom(e), opts.assumeChecked && p)
    }

    case Ensuring(body, l @ Lambda(Seq(res), pred)) => simplify(pred, path) match {
      case (BooleanLiteral(true), true) => simplify(body, path)
      case (rp, _) =>
        val (rb, _) = simplify(body, path)
        (Ensuring(rb, Lambda(Seq(res), rp).copiedFrom(l)).copiedFrom(e), false)
    }

    case MatchExpr(scrut, cases) =>
      val (rs, ps) = simplify(scrut, path)
      val (_, stop, purity, newCases) = cases.foldLeft((path, false, ps, Seq[MatchCase]())) {
        case (p @ (_, true, _, _), _) => p
        case ((soFar, _, purity, newCases), c @ MatchCase(pattern, guard, rhs)) =>
          simplify(conditionForPattern[Path](rs, pattern, includeBinders = false).fullClause, soFar) match {
            case (BooleanLiteral(false), true) => (soFar, false, purity, newCases)
            case (rc, pc) =>
              val path = conditionForPattern[Env](rs, pattern, includeBinders = true)
              val (rg, pg) = guard.map(simplify(_, soFar merge path)).getOrElse((BooleanLiteral(true), true))
              (and(rc, rg), pc && pg) match {
                case (BooleanLiteral(false), true) => (soFar, false, purity, newCases)
                case (BooleanLiteral(true), true) =>
                  // We know path withCond rg is true here but we need the binders
                  val bindings = conditionForPattern[Path](rs, pattern, includeBinders = true).bindings
                  val (rr, pr) = simplify(bindings.foldRight(rhs) { case ((i, e), b) => Let(i, e, b) }, soFar)
                  val lastCase = MatchCase(WildcardPattern(None).copiedFrom(pattern), None, rr).copiedFrom(c)
                  (soFar, true, purity && pr, newCases :+ lastCase)

                case (_, _) =>
                  val (rr, pr) = simplify(rhs, soFar merge (path withCond rg))
                  val newGuard = if (rg == BooleanLiteral(true)) None else Some(rg)
                  (
                    soFar merge (path withCond rg).negate,
                    false,
                    purity && pc && pg && pr,
                    newCases :+ MatchCase(pattern, newGuard, rr).copiedFrom(c)
                  )
              }
          }
      }

      newCases match {
        case Seq() => (
          Assert(
            BooleanLiteral(false).copiedFrom(e),
            Some("No valid case"),
            Choose(
              ValDef.fresh("res", e.getType).copiedFrom(e),
              BooleanLiteral(true).copiedFrom(e)
            ).copiedFrom(e)
          ).copiedFrom(e),
          opts.assumeChecked
        )

        case Seq(MatchCase(WildcardPattern(None), None, rhs)) if stop => (rhs, purity)
        case _ => (MatchExpr(rs, newCases).copiedFrom(e), purity)
      }

    case _ => super.simplify(e, path)
  }
}
