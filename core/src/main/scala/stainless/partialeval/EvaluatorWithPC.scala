/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package partialeval

import scala.language.existentials
import scala.concurrent.duration._
import scala.collection.mutable.{Map => MutableMap}
import scala.util.DynamicVariable

import inox.Context
import inox.utils._
import inox.solvers._
import inox.solvers.SolverResponses._
import inox.solvers.PurityOptions
import inox.evaluators.EvaluationResults

import stainless.transformers._

trait EvaluatorWithPC extends SimplifierWithPC { self =>

  import trees._
  import symbols._
  import dsl._
  import exprOps._

  val context: Context
  val semantics: Semantics
  import context.reporter

  override val opts = PurityOptions(context)

  implicit val debugSection = partialeval.DebugSectionPartialEval

  protected lazy val maxSteps: Int = context.options.findOptionOrDefault(inox.evaluators.optMaxCalls)

  protected var stepsTaken: Int = 0

  private[this] var dynUnfold: DynamicVariable[List[Boolean]] = new DynamicVariable(Nil)

  def eval(expr: Expr): Expr = {
    stepsTaken = 0

    val res = transform(expr)
    res
  }

  override protected def simplify(expr: Expr, path: CNFPath): (Expr, Boolean) = {
    stepsTaken += 1

    if (stepsTaken >= maxSteps || context.interruptManager.isInterrupted) {
      return (expr, opts.assumeChecked)
    }

    // Base + when inline fn
    simplifyGround(expr)(semantics, context) match {
      case Require(pred, body) => simplify(pred, path) match {
        case (BooleanLiteral(true), true) => simplify(body, path)
        case (BooleanLiteral(false), true) =>
          val (rb, _) = simplify(body, path)
          (Require(BooleanLiteral(false).copiedFrom(expr), rb).copiedFrom(expr), opts.assumeChecked)
        case (rp, _) =>
          val (rb, _) = simplify(body, path withCond rp)
          (Require(rp, rb).copiedFrom(expr), opts.assumeChecked)
      }

      case m @ MatchExpr(scrut, cases) =>
        // println(s"\n Evaluating match over $scrut under path $path\n")
        val (rs, ps) = simplify(scrut, path)
        val (_, _, purity, newCases) = simplifyMatchCases(cases, rs, ps, path, simplifyCases = false)
        val matches = newCases.toStream.map { c =>
          matchesCase(rs, c)(path).map(c -> _)
        }

        matches.find(_.nonEmpty) match {
          case Some(Some((c, (mapping, guard)))) =>
            val subPath = guard.map(path withCond _).getOrElse(path)
            simplify(mappingToLet(mapping, c.rhs), subPath)
          case _ =>
            (MatchExpr(rs, cases), purity)
        }

      case fi @ FunctionInvocation(id, tps, args) =>
        val fd = fi.tfd
        val (Seq(pre, post), body) = deconstructSpecs(fd.fullBody) // FIXME
        val (rargs, pa) = args.map(simplify(_, path)).unzip
        val pred = fd.params.zip(rargs).foldRight(pre.expr) {
          case ((vd, arg), acc) => Let(vd, arg, acc)
        }

        unfold(fi, rargs, path withCond pred) match {
          case Some(res) =>
            // reporter.debug(s"Unfolded ${FunctionInvocation(id, tps, rargs)} (previously $fi)")
            simplify(Assume(pred, res), path)
          case None => (FunctionInvocation(id, tps, rargs), pa.foldLeft(true)(_ && _))
        }

      case Ensuring(body, post) =>
        val (rb, pb) = simplify(body, path)
        (Ensuring(rb, post).toAssert, pb)

      case e =>
        super.simplify(e, path)
    }
  }

  protected def unfold(fi: FunctionInvocation, rargs: Seq[Expr], path: CNFPath): Option[Expr] = {
    val tfd = fi.tfd
    if (tfd.fd.flags.contains("extern")) {
      return None
    }

    lazy val subst = freshenLocals(tfd.withParamSubst(rargs, tfd.fullBody))

    if (!dynUnfold.value.headOption.getOrElse(true)) {
      return None
    }

    if (isRecursive(fi.id)) {
      if (isProductiveUnfolding(fi.id, subst, path)) {
        Some(assumePostcondition(tfd, subst, rargs, path))
      } else {
        None
      }
    } else {
      Some(assumePostcondition(tfd, subst, rargs, path))
    }
  }

  protected def assumePostcondition(tfd: TypedFunDef, result: Expr, args: Seq[Expr], path: CNFPath): Expr = {
    tfd.postcondition match {
      case Some(Lambda(Seq(vd), post)) =>
        freshenLocals(Let(vd, result, Assume(tfd.withParamSubst(args, post), vd.toVariable)))
      case None =>
        result
    }
  }

  protected def isProductiveUnfolding(id: Identifier, expr: Expr, path: CNFPath): Boolean = {
    def isKnown(expr: Expr): Boolean = expr match {
      case BooleanLiteral(_) => true
      case _ => false
    }

    val invocationPaths = collectWithPC(expr) {
      case (fi: FunctionInvocation, subPath) if fi.id == id || transitivelyCalls(fi.id, id) => subPath
    }

    dynUnfold.value = false :: dynUnfold.value
    val simplePaths = invocationPaths.map(p => simplify(p.toClause, path)._1)
    val known = simplePaths.forall(isKnown)
    dynUnfold.value = dynUnfold.value.tail

    known
  }

  protected def mappingToLet(mapping: Map[ValDef, Expr], body: Expr): Expr = {
    mapping.toSeq.foldRight(body) { case ((vd, e), acc) => Let(vd, e, acc) }
  }

  private def matchesCase(scrut: Expr, caze: MatchCase)
                         (path: CNFPath, allowWildcards: Boolean = false): Option[(Map[ValDef, Expr], Option[Expr])] = {

    def obind(ob: Option[ValDef], e: Expr): Map[ValDef, Expr] = {
      Map.empty[ValDef, Expr] ++ ob.map(_ -> e)
    }

    def matchesPattern(pat: Pattern, expr: Expr, allowWildcards: Boolean): Option[Map[ValDef, Expr]] = (pat, expr) match {
      case (WildcardPattern(ob), e) if allowWildcards =>
        Some(obind(ob, e))

      case (LiteralPattern(ob, lit), e) if lit == e =>
        Some(obind(ob, e))

      case (ADTPattern(ob, id, tps, subs), ADT(id2, tps2, args)) =>
        if (id == id2 && tps == tps2) {
          val res = (subs zip args) map (p => matchesPattern(p._1, p._2, true))
          if (res.forall(_.isDefined)) {
            Some(obind(ob, expr) ++ res.flatten.flatten)
          } else None
        } else None

      case (TuplePattern(ob, subs), Tuple(args)) =>
        if (subs.size == args.size) {
          val res = (subs zip args) map (p => matchesPattern(p._1, p._2, true))
          if (res.forall(_.isDefined)) {
            Some(obind(ob, expr) ++ res.flatten.flatten)
          } else {
            None
          }
        } else {
          None
        }

      case (up @ UnapplyPattern(ob, rc, id, tps, subs), scrut) =>
        val (eRec, _) = rc.map(e => simplify(e, path)).unzip
        val (unapp, _) = simplify(FunctionInvocation(id, tps, eRec.toSeq :+ scrut), path)
        simplify(up.getIsEmpty.applied(Seq(unapp)), path)._1 match {
          case BooleanLiteral(false) =>
            val extracted = simplify(up.getGet.applied(Seq(unapp)), path)._1
            val res = (subs zip unwrapTuple(extracted, subs.size)) map (p => matchesPattern(p._1, p._2, true))
            if (res.forall(_.isDefined)) {
              Some(obind(ob, expr) ++ res.flatten.flatten)
            } else {
              None
            }
          case BooleanLiteral(true) => None
          case other => None
        }

      case _ => None
    }

    matchesPattern(caze.pattern, scrut, allowWildcards).flatMap { mapping =>
      caze.optGuard match {
        case Some(guard) =>
          val fullGuard = mappingToLet(mapping, guard)
          val (res, _) = simplify(fullGuard, path)
          if (res == BooleanLiteral(true)) {
            Some((mapping, Some(fullGuard)))
          } else {
            None
          }
        case None =>
          Some((mapping, None))
      }
    }
  }

}
