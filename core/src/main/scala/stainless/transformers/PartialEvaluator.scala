/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package transformers

import scala.language.existentials
import scala.concurrent.duration._
import scala.collection.mutable.{Map => MutableMap}
import scala.util.DynamicVariable

import inox.{Context, Semantics}
import inox.utils._
import inox.solvers._
import inox.solvers.SolverResponses._
import inox.evaluators.EvaluationResults

import stainless.transformers._

object DebugSectionPartialEval extends inox.DebugSection("partial-eval")

trait PartialEvaluator extends SimplifierWithPC { self =>
  implicit val context: inox.Context
  protected val semantics: inox.SemanticsProvider { val trees: self.trees.type }

  import trees._
  import symbols.{simplifier => _, _}
  import exprOps._
  import dsl._

  import context.reporter

  protected implicit val debugSection = DebugSectionPartialEval

  override protected def simplify(e: Expr, path: Env): (Expr, Boolean) = e match {
    case b: BooleanLiteral => (b, true)

    case fi @ FunctionInvocation(id, tps, args) if canUnfold(fi.id) && !fi.tfd.fd.flags.contains(Extern) =>
      val (rargs, pargs) = args.map(simplify(_, path)).unzip

      unfold(fi, rargs, path) match {
        case Some(unfolded) => simplify(unfolded, path)
        case None => (FunctionInvocation(id, tps, rargs), pargs.foldLeft(true)(_ && _))
      }

    case Require(pred, body) => simplify(pred, path) match {
      case (BooleanLiteral(true), true) => simplify(body, path)
      case (BooleanLiteral(false), true) =>
        val (rb, _) = simplify(body, path)
        (Require(BooleanLiteral(false).copiedFrom(e), rb).copiedFrom(e), opts.assumeChecked)
      case (rp, _) =>
        val (rb, _) = simplify(body, path withCond rp)
        (Require(rp, rb).copiedFrom(e), opts.assumeChecked)
    }

    case Application(e, es)  =>
      val (caller, recons): (Expr, Expr => Expr) = simplify(e, path) match {
        case (Assume(pred, e), _) => (e, assume(pred, _))
        case (e, _) => (e, expr => expr)
      }

      path.expand(caller) match {
        case (l: Lambda) =>
          simplify(recons(l.withParamSubst(es, l.body)), path)
        case _ =>
          val (res, _) = es.map(simplify(_, path)).unzip
          (application(caller, res), opts.assumeChecked)
      }

    case _ => super.simplify(e, path)
  }

  private[this] var doNotUnfold: Set[Identifier] = Set.empty
  private[this] def canUnfold(id: Identifier): Boolean = !doNotUnfold.contains(id)

  private[this] val maxUnfoldingSteps: Int = 50
  private[this] var unfoldingStepsLeft: Map[Identifier, Int] = Map.empty.withDefault(_ => maxUnfoldingSteps)

  protected def unfold(fi: FunctionInvocation, args: Seq[Expr], path: Env): Option[Expr] = {
    lazy val unfolded = exprOps.freshenLocals(fi.tfd.withParamSubst(args, fi.tfd.fullBody))

    if (unfoldingStepsLeft(fi.id) > 0 && (!isRecursive(fi.id) || isProductiveUnfolding(fi.id, unfolded, path))) {
      decreaseUnfoldingStepsLeft(fi.id)
      Some(unfolded)
    } else {
      None
    }
  }

  protected def decreaseUnfoldingStepsLeft(id: Identifier): Unit = {
    val left = unfoldingStepsLeft(id)
    unfoldingStepsLeft = unfoldingStepsLeft.updated(id, left - 1)
  }

  protected def preventUnfolding[A](id: Identifier)(action: => A): A = {
    val alreadyPrevented = doNotUnfold contains id
    if (!alreadyPrevented) doNotUnfold = doNotUnfold + id
    val res = action
    if (!alreadyPrevented) doNotUnfold = doNotUnfold - id
    res
  }

  protected def isProductiveUnfolding(id: Identifier, expr: Expr, path: Env): Boolean = {
    def isKnown(expr: Expr): Boolean = expr match {
      case BooleanLiteral(_) => true
      case _ => false
    }

    val invocationPaths = collectWithPC(expr) {
      case (fi: FunctionInvocation, subPath) if fi.id == id || transitivelyCalls(fi.id, id) => subPath
    }

    preventUnfolding(id) {
      invocationPaths.map(p => transform(p.toClause, path)).forall(isKnown)
    }
  }

}

trait FastPartialEvaluator extends PartialEvaluator with inox.transformers.SimplifierWithCNFPath {
  override type Env = CNFPath
  override implicit def pp = CNFPath
}

trait SlowPartialEvaluator extends PartialEvaluator { self =>

  import trees._
  import symbols._

  import context.reporter

  val program = inox.Program(trees)(symbols)
  val solver = semantics.getSemantics(program).getSolver(context).withTimeout(150.millis).toAPI

  class SlowPath private[SlowPartialEvaluator] (
    val path: Path
  ) extends PathLike[SlowPath] with SolvingPath {

    override def implies(cond: Expr): Boolean = {
      if (cond.getType != BooleanType()) return false
      solver.solveVALID(path implies cond).getOrElse(false)
    }

    override def merge(that: SlowPath): SlowPath = new SlowPath(path merge that.path)
    override def negate: SlowPath = new SlowPath(path.negate)
    override def withBinding(p: (ValDef, Expr)): SlowPath = new SlowPath(path withBinding p)
    override def withBound(b: ValDef): SlowPath = new SlowPath(path withBound b)
    override def withCond(e: Expr): SlowPath = new SlowPath(path withCond e)

    override def toString: String = path.toString
  }

  implicit object SlowPath extends PathProvider[SlowPath] {
    override val empty = new SlowPath(Path.empty)
    def apply(path: Path) = new SlowPath(path)
  }

  override type Env = SlowPath
  override def initEnv = SlowPath.empty
  override implicit def pp = SlowPath
}

