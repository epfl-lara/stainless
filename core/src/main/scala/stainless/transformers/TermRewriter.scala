/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package transformers

import scala.language.existentials
import scala.concurrent.duration._
import scala.collection.mutable.{Map => MutableMap}

import inox.{Context, Semantics}
import inox.utils._
import inox.solvers._
import inox.solvers.SolverResponses._
import inox.evaluators.EvaluationResults

trait TermRewriter extends SimplifierWithPC { self =>
  import trees._
  import symbols.{simplifier => _, _}
  import exprOps._
  import dsl._

  val rulesFuns: List[FunDef]

  lazy val rewriteRules: List[RewriteRule] =
    rulesFuns.flatMap(toRewriteRule)

  class RewriteRule(fd: FunDef, val lhs: Expr, val rhs: Expr) {
    val name: Identifier = fd.id
    val params: Seq[ValDef] = fd.params
    val hyp: Option[Expr] = preconditionOf(fd.fullBody)

    private def subst(args: Seq[Expr], expr: Expr): Expr = {
      require(args.size == params.size)

      val subst = fd.params.zip(args).toMap

      val tpSubst = fd.params.map(_.tpe).zip(args.map(_.getType))
        .foldLeft(Map.empty[TypeParameter, Type]) { case (acc, (l, r)) =>
          acc ++ instantiation(l, r).getOrElse(Map.empty)
        }

      freshenLocals(typeOps.instantiateType(replaceFromSymbols(subst, expr), tpSubst))
    }

    def substRHS(args: Seq[Expr]): Expr = subst(args, rhs)
    def substHyp(args: Seq[Expr]): Expr = hyp match {
      case None => BooleanLiteral(true)
      case Some(b @ BooleanLiteral(_)) => b
      case Some(hyp) => subst(args, hyp)
    }
  }

  protected def toRewriteRule(fd: FunDef): Option[RewriteRule] =
    withoutSpecs(fd.fullBody) flatMap {
      case Equals(lhs, rhs) => Some(new RewriteRule(fd, lhs, rhs))
      case _ => None
    }

  private class Unsolvable extends Exception
  private def unsolvable = throw new Unsolvable

  private def unificationConstraints(a: Expr, b: Expr, free: Set[Variable]): List[(Variable, Expr)] = (a, b) match {
    case (a: Terminal, b: Terminal) if a == b =>
      Nil

    case (a: Variable, b) if !(exprOps.variablesOf(b) contains a) =>
      List(a -> b)

    case (_: Variable, _) => unsolvable
    case (_, _: Variable) => unsolvable

    case (a, b) if a.getClass == b.getClass =>
    val Operator(as, _) = a
    val Operator(bs, _) = b

    if (as.size == bs.size) {
      as.zip(bs).toList flatMap { case (aa, bb) =>
        unificationConstraints(aa, bb, free)
      }
    }
    else unsolvable

    case _ => unsolvable
  }

  private def unificationSolution(const: List[(Variable, Expr)]): List[(Variable, Expr)] = const match {
    case Nil => Nil

    case (v, e) :: tl =>
      val replaced = tl map { case (v1, e2) =>
        val subst = Map(v -> e)
        (v1, exprOps.replace(Map(v -> e), e2))
      }

      (v -> e) :: unificationSolution(replaced)
  }

  private def unify(a: Expr, b: Expr, free: Set[Variable]): Option[Map[Variable, Expr]] = {
    if (a == b) return Some(Map.empty)

    try {
      val constraints = unificationConstraints(a, b, free)
      // println(s"CONSTRAINTS: $constraints")
      val sol = unificationSolution(constraints)
      // println(s"SOLUTION: $sol")
      Some(sol.toMap)
    } catch {
      case _: Unsolvable => None
    }
  }

  private var rulesApplied: Set[Identifier] = Set.empty

  def rewrite(e: Expr): (Expr, Set[Identifier]) = {
    rulesApplied = Set.empty
    val (res, _) = simplify(e, initEnv)
    val toReturn = (res, rulesApplied)
    rulesApplied = Set.empty
    toReturn
  }

  private def rewrite(e: Expr, path: Env): Expr = {
    val free = variablesOf(e)

    val res = rewriteRules.foldLeft(e) { case (e, rule) =>
      // println(s"\n\nUNIFYING:")
      // println(s" - LHS: ${rule.lhs}")
      // println(s" - EXPR: ${e}")
      // println(s" - HYP: ${rule.hyp}")
      // println(s" - RHS: ${rule.rhs}")

      val subst = unify(rule.lhs, e, free)
      // println(s"SUBST: $subst")

      val res = subst flatMap { case subst =>
        val args = rule.params.map(vd => subst.getOrElse(vd.toVariable, vd.toVariable))
        val hypothesis = simplify(rule.substHyp(args), path)._1
        // println(s" - HYP: ${rule.substHyp(args)}")
        // println(s" - SIMPLE HYP: $hypothesis")
        // println(s" - IMPLIED: ${path implies hypothesis}")

        hypothesis match {
          case BooleanLiteral(true) =>
            rulesApplied = rulesApplied + rule.name
            Some(rule.substRHS(args))
          case _ => None
        }
      }

      // println(s"RESULT: $res")
      // println()

      res.getOrElse(e)
    }

    // println("BEFORE: " + e)
    // println("AFTER: " + res)
    // println("\n\n")
    res
  }

  override protected def simplify(e: Expr, path: Env): (Expr, Boolean) = {
    val (after, pure) = super.simplify(e, path)

    val res = inox.utils.fixpoint { (e: Expr) =>
      rewrite(e, path)
    } (after)

    (res, pure)
  }
}

