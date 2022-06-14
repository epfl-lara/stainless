package stainless
package transformers
package lattices

import inox.solvers

trait OL extends Core {
  import trees._
  import symbols.{given, _}
  import Opaques.{given, _}
  import Purity._
  import scala.collection.mutable

  private val leqCache = mutable.Map.empty[(Code, Code), Boolean]

  override final def impliedImpl(rhs: Code)(using env: Env, ctxs: Ctxs): Boolean = {
    val lhsConj = conjunct(ctxs.allConds)
    latticesLeq(lhsConj, rhs)
  }

  final def latticesLeq(lhs: Code, rhs: Code): Boolean = {
    if (lhs == rhs) true
    else leqCache.getOrElseUpdate((lhs, rhs), (code2sig(lhs), code2sig(rhs)) match {
      case (BoolLitSig(b), _) => !b
      case (_, BoolLitSig(b)) => b

      case (OrSig(disjs1, false), OrSig(disjs2, true)) =>
        disjs1.exists(c => latticesLeq(negCodeOf(c), rhs)) || disjs2.exists(latticesLeq(lhs, _))

      case (_, OrSig(disjs, false)) =>
        disjs.forall(d => latticesLeq(lhs, negCodeOf(d)))

      case (OrSig(disjs, true), _) =>
        disjs.forall(latticesLeq(_, rhs))

      case (_, OrSig(disjs, true)) =>
        disjs.exists(latticesLeq(lhs, _))

      case (OrSig(disjs, false), _) =>
        disjs.exists(c => latticesLeq(negCodeOf(c), rhs))

      case (EqSig(lhs1, rhs1), LeqSig(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2
      case (EqSig(lhs1, rhs1), GeqSig(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2
      case (LtSig(lhs1, rhs1), LeqSig(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2
      case (GtSig(lhs1, rhs1), GeqSig(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2

      case (LtSig(lhs1, rhs1), NotSig(EqCode(lhs2, rhs2))) => lhs1 == lhs2 && rhs1 == rhs2
      case (GtSig(lhs1, rhs1), NotSig(EqCode(lhs2, rhs2))) => lhs1 == lhs2 && rhs1 == rhs2

      case _ => false
    })
  }

  override final def doSimplifyDisjunction(disjs: Seq[Code], polarity: Boolean)(using Env, Ctxs): Seq[Code] = {
    if (disjs.size <= 1) return disjs

    val nonSimp = {
      val or = codeOfDisjs(disjs)
      if (polarity) or
      else codeOfSig(mkNot(or), BoolTy)
    }

    def treatChild(phiKs: Code): Seq[Code] = code2sig(phiKs) match {
      case OrSig(psiJs, true) => psiJs
      case OrSig(psiJs, false) =>
        if (polarity) {
          findMap(psiJs) { psiJ =>
            val neg = negCodeOf(psiJ)
            if (latticesLeq(neg, nonSimp)) Some(treatChild(neg))
            else None
          }.getOrElse(Seq(phiKs))
        } else {
          findMap(psiJs) { psiJ =>
            if (latticesLeq(nonSimp, psiJ)) Some(treatChild(negCodeOf(psiJ)))
            else None
          }.getOrElse(Seq(phiKs))
        }
      case _ => Seq(phiKs)
    }

    def rec(remaining: Seq[Code], accepted: Seq[Code]): Seq[Code] = remaining match {
      case Seq() => accepted
      case current +: remaining =>
        if (remaining.size + accepted.size == 0) Seq(current)
        else {
          val all = codeOfDisjs(remaining ++ accepted)
          val accept = !latticesLeq(current, all) || !codePurity(current).isPure
          rec(remaining, if (accept) accepted :+ current else accepted)
        }
    }

    val disjs2 = disjs.flatMap(treatChild)
    rec(disjs2, Seq.empty)
  }

  // (We denote disjunctions phi_1,...,phi_n)
  // If it exists i s.t.
  //   ¬phi_i <= \/_j phi_j    (1)
  // we then return the index max(i, k) s.t.
  //   ¬phi_i <= phi_k         (2)
  //
  // Note: we obtain that:
  //   ¬phi_i \/ \/_j phi_j === true        (by ¬phi_i \/ phi_i)
  //                        === \/_j phi_j  (by (1))
  // The existence of i by (1) implies \/_j phi_j === true
  // In our case, we are not allowed to drop *all* phi_j (due to presence of impure expressions).
  // As such, we are interested in finding a k s.t. \/_j<=k phi_j === true (we can then drop everything after this k, including impure expressions).
  // The max(i, k) of (2) is exactly what we need.
  // Indeed, by (1) we have ¬phi_i <= \/_j phi_j ==> ∃k. ¬phi_i <= phi_k
  // (see definition of <=, case disjunction on the right).
  override final def checkForDisjunctionContradiction(disjs: Seq[Code])(using Env, Ctxs): Option[Int] = {
    assert(disjs.size >= 2)
    val negDisjs = disjs map negCodeOf
    val disjsCode = codeOfDisjs(disjs)
    for {
      i <- indexWhereOpt(negDisjs)(latticesLeq(_, disjsCode))
      negPhiI = negDisjs(i)
      k <- indexWhereOpt(disjs)(latticesLeq(negPhiI, _))
    } yield math.max(i, k)
  }
}

object OL {
  def apply(t: ast.Trees, s: t.Symbols, opts: solvers.PurityOptions): OL{val trees: t.type; val symbols: s.type} = {
    class Impl(override val trees: t.type, override val symbols: s.type, override val opts: solvers.PurityOptions) extends OL
    new Impl(t, s, opts)
  }
}