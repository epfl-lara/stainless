package stainless
package transformers
package lattices

import inox.solvers

trait OCBSL extends Core {
  import trees._
  import symbols.{given, _}
  import Opaques.{given, _}
  import Purity._

  override final def impliedImpl(rhs: Code)(using env: Env, ctxs: Ctxs): Boolean = {
    // a ==> b === a && b = a
    val lhsConj = conjunct(ctxs.allConds)
    val rhsLhsConj = conjunct(Seq(lhsConj, rhs))
    rhsLhsConj == lhsConj
  }

  override final def doSimplifyDisjunction(disjs: Seq[Code], polarity: Boolean)(using Env, Ctxs): Seq[Code] = disjs

  override final def checkForDisjunctionContradiction(disjs0: Seq[Code])(using Env, Ctxs): Option[Int] = {
    val disjs = denormalize(disjs0)
    checkForContradiction(disjs) match {
      case Right(ix) => Some(ix)
      case Left((_, neg)) =>
        val found = neg.exists { negC =>
          code2sig(negC) match {
            case Signature(Label.Or, negDisj) =>
              denormalize(negDisj).forall(disjs.contains)
            case _ => false
          }
        }
        if (found) Some(disjs.length - 1) else None
    }
  }

  private def checkForContradiction(cs: Seq[Code]): Either[(Set[Code], Set[Code]), Int] = {
    def rec(i: Int, pos: Set[Code], neg: Set[Code]): Either[(Set[Code], Set[Code]), Int] = {
      if (i == cs.length) Left((pos, neg))
      else {
        val c = cs.head
        code2sig(c) match {
          case Signature(Label.Not, Seq(cc)) =>
            if (pos(cc)) Right(i)
            else rec(i + 1, pos, neg + cc)
          case _ =>
            if (neg(c)) Right(i)
            else rec(i + 1, pos + c, neg)
        }
      }
    }
    rec(0, Set.empty, Set.empty)
  }

  // Convert a >= b and a > b to !(a < b) and !(a <= b) respectively.
  // This will ease the work of for checkForDisjunctionContradiction and checkForConjunctionContradiction.
  // Assumes that `cs` is normalized (i.e. we have `a` instead of !!a, a <= b instead of !(a > b) etc.)
  // so in some sense we are denormalizing parts of the given `cs`.
  // If `cs` is not normalized, `denormalize` may return expressions such as !!(a > b),
  // which may cause a contradiction to be missed (but it is not unsound).
  private def denormalize(cs: Seq[Code]): Seq[Code] = {
    cs.map { c =>
      code2sig(c) match {
        case GeqSig(a, b) =>
          val lt = codeOfSig(mkLessThan(a, b), BoolTy)
          codeOfSig(mkNot(lt), BoolTy)
        case GtSig(a, b) =>
          val leq = codeOfSig(mkLessEquals(a, b), BoolTy)
          codeOfSig(mkNot(leq), BoolTy)
        case _ => c
      }
    }
  }
}

object OCBSL {
  def apply(t: ast.Trees, s: t.Symbols, opts: solvers.PurityOptions): OCBSL{val trees: t.type; val symbols: s.type} = {
    class Impl(override val trees: t.type, override val symbols: s.type, override val opts: solvers.PurityOptions) extends OCBSL
    new Impl(t, s, opts)
  }
}