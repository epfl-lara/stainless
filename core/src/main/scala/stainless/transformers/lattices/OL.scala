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

  private val leqCacheThreshold = 50000
  private val leqCache = mutable.Map.empty[(Code, Code), Boolean]

  override final def impliedImpl(rhs: Code)(using env: Env, ctxs: Ctxs): Boolean = {
    val lhsConj = conjunct(ctxs.allConds)
    latticesLeq(lhsConj, rhs)
  }

  override def clearCaches(): Unit = {
    super.clearCaches()
    if (leqCache.size > leqCacheThreshold) {
      leqCache.clear()
    }
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

      case (ArithRel(lhs, lhsKind), ArithRel(rhs, rhsKind)) =>
        arithLeq(ArithRel(lhs, lhsKind), ArithRel(rhs, rhsKind))

      // i == j ==> a(i) == a(j)
      case (EqSig(i, j), EqSig(ArraySelCode(a1, ii), ArraySelCode(a2, jj))) => a1 == a2 && i == ii && j == jj
      // i == j ==> a[i := v](j) == v
      //            a[j := v](i) == v
      case (EqSig(i, j), EqSig(ArraySelCode(ArrayUpdCode(_, updIx, v1), selIx), v2)) => v1 == v2 && ((updIx == i && selIx == j) || (updIx == j && selIx == i))
      // i != j ==> a[i := v](j) = a(j)
      //            a[j := v](i) = a(i)
      case (NotSig(EqCode(i, j)), EqSig(c1, c2)) =>
        def leq(a1: Code, updIx: Code, selIx1: Code, a2: Code, selIx2: Code): Boolean =
          a1 == a2 && selIx1 == selIx2 && ((updIx == i && selIx1 == j) || (updIx == j && selIx1 == i))

        (code2sig(c1), code2sig(c2)) match {
          case (ArraySelSig(ArrayUpdCode(a1, updIx, _), selIx1), ArraySelSig(a2, selIx2)) => leq(a1, updIx, selIx1, a2, selIx2)
          case (ArraySelSig(a2, selIx2), ArraySelSig(ArrayUpdCode(a1, updIx, _), selIx1)) => leq(a1, updIx, selIx1, a2, selIx2)
          case _ => false
        }

      case (Signature(Label.IfExpr, Seq(cond, thn, els)), _) =>
        latticesLeq(adaptIf(cond, thn, els), rhs)

      case (_, Signature(Label.IfExpr, Seq(cond, thn, els))) =>
        latticesLeq(lhs, adaptIf(cond, thn, els))

      case _ => false
    })
  }

  enum ArithRelKind {
    case Eq
    case Neq
    case Lt
    case Leq
  }
  // rhs is always 0
  case class ArithRel(lhs: LinComb, kind: ArithRelKind)
  object ArithRel {
    def unapply(sig: Signature): Option[ArithRel] = {
      val (lhs, rhs, kind) = sig match {
        case EqSig(lhs, rhs) => (lhs, rhs, ArithRelKind.Eq)
        case LeqSig(lhs, rhs) => (lhs, rhs, ArithRelKind.Leq)
        case LtSig(lhs, rhs) => (lhs, rhs, ArithRelKind.Lt)
        case GeqSig(lhs, rhs) => (rhs, lhs, ArithRelKind.Leq)
        case GtSig(lhs, rhs) => (rhs, lhs, ArithRelKind.Lt)
        case NotSig(EqCode(lhs, rhs)) => (lhs, rhs, ArithRelKind.Neq)
        case _ => return None
      }
      assert(codeTpe(lhs) == codeTpe(rhs))
      if (isIntLikeType(lhs)) // Guard against RealType
        Some(ArithRel(toLinComb(lhs) - toLinComb(rhs), kind))
      else None
    }
  }

  final def arithLeq(lhs: ArithRel, rhs: ArithRel): Boolean = {
    if (lhs.lhs.tpe != rhs.lhs.tpe) {
      return false
    }
    val unbounded = lhs.lhs.tpe == IntegerType()
    val diff = lhs.lhs - rhs.lhs
    diff.terms.isEmpty && ((lhs.kind, rhs.kind) match {
      case (ArithRelKind.Neq, ArithRelKind.Neq) => diff.cst == 0
      case (ArithRelKind.Eq, ArithRelKind.Eq) => diff.cst == 0
      // x + a <= 0  ==> x + b <= 0  <==   a >= b
      case (ArithRelKind.Leq, ArithRelKind.Leq) =>
        if (unbounded) diff.cst >= 0
        else diff.cst == 0
      // x + a < 0   ==> x + b < 0   <==   a >= b
      case (ArithRelKind.Lt, ArithRelKind.Lt) =>
        if (unbounded) diff.cst >= 0
        else diff.cst == 0

      // x + a <= 0  ==> x + b < 0   <==   a >= b + 1
      case (ArithRelKind.Leq, ArithRelKind.Lt) =>
        if (unbounded) diff.cst >= 1
        else diff.cst == 1
      // x + a < 0   ==> x + b <= 0  <==   a >= b - 1
      case (ArithRelKind.Lt, ArithRelKind.Leq) =>
        if (unbounded) diff.cst >= -1
        else diff.cst == -1

      // x + a < 0 ==> x + b != 0    <==   a == b
      case (ArithRelKind.Lt, ArithRelKind.Neq) => diff.cst == 0

      // x + a == 0 ==> x + b <= 0   <==   a >= b
      case (ArithRelKind.Eq, ArithRelKind.Leq) =>
        if (unbounded) diff.cst >= 0
        else diff.cst == 0
      // x + a == 0 ==> x + b < 0    <==   a >= b + 1
      case (ArithRelKind.Eq, ArithRelKind.Lt) =>
        if (unbounded) diff.cst >= 1
        else diff.cst == 1

      case _ => false
    })
  }

  override final def doSimplifyDisjunction(disjs: Seq[Code], polarity: Boolean)(using env: Env, ctxs: Ctxs): Seq[Code] = {
    if (disjs.size <= 1 || env.forceBinding) return disjs

    val nonSimp = {
      val or = codeOfDisjs(disjs)
      if (polarity) or
      else codeOfSig(mkNot(or), BoolTy)
    }

    // An expression must be pure in order to be dropped
    def canBeDropped(c: Code): Boolean = {
      val isPure = codePurity(c).isPure
      code2sig(c) match {
        case OrSig(disjs, _) =>
          // For disjunctions, we furthermore require that all of their disjunctions to be pure as well.
          // Note that if `c` is bound, it is considered pure even though its disjunction are impure.
          isPure && disjs.forall(codePurity(_).isPure)

        case _ => isPure
      }
    }

    def treatChild(phiKs: Code): Seq[Code] = code2sig(phiKs) match {
      case OrSig(psiJs, true) => psiJs
      case OrSig(psiJs, false) =>
        val psiJsDropability = psiJs.map(canBeDropped)
        if (polarity) {
          findMap(psiJs.zipWithIndex) { case (psiJ, j) =>
            val doTreatChild = psiJsDropability.zipWithIndex.forall {
              // We drop the other psiJ if we meet these two conditions
              // -The other psiJs can be dropped (i.e. are pure)
              // -The current psiJ that we will keep is already bound (i.e. "evaluated")
              case (drop, k) => drop || (j == k && ctxs.isBoundDef(psiJ))
            }
            val neg = negCodeOf(psiJ)
            if (doTreatChild && latticesLeq(neg, nonSimp)) Some(treatChild(neg))
            else None
          }.getOrElse(Seq(phiKs))
        } else {
          findMap(psiJs.zipWithIndex) { case (psiJ, j) =>
            val doTreatChild = psiJsDropability.zipWithIndex.forall {
              case (drop, k) => drop || (j == k && ctxs.isBoundDef(psiJ))
            }
            if (doTreatChild && latticesLeq(nonSimp, psiJ)) Some(treatChild(negCodeOf(psiJ)))
            else None
          }.getOrElse(Seq(phiKs))
        }
      case _ => Seq(phiKs)
    }

    val disjs2 = disjs.flatMap(treatChild)
    val disjs2Dropability = disjs2.forall(canBeDropped)

    def rec(remaining: Seq[Code], accepted: Seq[Code]): Seq[Code] = remaining match {
      case Seq() => accepted
      case current +: remaining =>
        if (remaining.size + accepted.size == 0) Seq(current)
        else {
          val all = codeOfDisjs(remaining ++ accepted)
          val accept = !disjs2Dropability || !latticesLeq(current, all)
          rec(remaining, if (accept) accepted :+ current else accepted)
        }
    }

    rec(disjs2, Seq.empty).distinct
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
    indexWhereOpt(negDisjs)(latticesLeq(_, disjsCode)).map { i =>
      val negPhiI = negDisjs(i)
      val k = indexWhereOpt(disjs)(latticesLeq(negPhiI, _))
        .getOrElse(disjs.length - 1)
      math.max(i, k)
    }
  }

  private def adaptIf(cond: Code, thn: Code, els: Code): Code = {
    // cond ==> thn && !cond ==> els
    // !cond \/ thn && cond \/ els
    // !(!(cond \/ thn) \/ !(cond \/ els))
    val thnPart = codeOfSig(mkOr(Seq(negCodeOf(cond), thn)), BoolTy)
    val elsPart = codeOfSig(mkOr(Seq(cond, els)), BoolTy)
    val disj = codeOfSig(mkOr(Seq(negCodeOf(thnPart), negCodeOf(elsPart))), BoolTy)
    negCodeOf(disj)
  }
}

object OL {
  def apply(t: ast.Trees, s: t.Symbols, opts: solvers.PurityOptions): OL{val trees: t.type; val symbols: s.type} = {
    class Impl(override val trees: t.type, override val symbols: s.type, override val opts: solvers.PurityOptions) extends OL
    new Impl(t, s, opts)
  }
}