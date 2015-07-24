/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package codegen.runtime

import utils._
import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps.valuateWithModel
import purescala.Constructors._
import solvers.SolverFactory

import java.util.WeakHashMap
import java.lang.ref.WeakReference
import scala.collection.mutable.{HashMap => MutableMap}
import scala.concurrent.duration._

import codegen.CompilationUnit

import synthesis._

object SolverEntryPoint {
  implicit val debugSection = DebugSectionSolver

  private case class ExprId(id: Int)
  private case class SolverProblem(args: Seq[Identifier], problem: Expr)

  private[this] val context = new WeakHashMap[ExprId, (WeakReference[CompilationUnit], SolverProblem)]()
  private[this] val cache   = new WeakHashMap[ExprId, MutableMap[Seq[AnyRef], Option[java.lang.Object]]]()

  private[this] val ids = new WeakHashMap[CompilationUnit, MutableMap[SolverProblem, ExprId]]()

  private[this] var _next = 0
  private[this] def nextInt(): Int = {
    _next += 1
    _next
  }

  private def getUniqueId(unit: CompilationUnit, p: SolverProblem): ExprId = {
    if (!ids.containsKey(unit)) {
      ids.put(unit, new MutableMap())
    }

    if (ids.get(unit) contains p) {
      ids.get(unit)(p)
    } else {
      val cid = new ExprId(nextInt())
      ids.get(unit) += p -> cid
      cid
    }
  }

  def register(args: Seq[Identifier], expr: Expr, unit: CompilationUnit): Int = {
    val p = SolverProblem(args, expr)
    val cid = getUniqueId(unit, p)

    context.put(cid, new WeakReference(unit) -> p)

    cid.id
  }

  def check(i: Int, inputs: Array[AnyRef]): Boolean = {
    val id = ExprId(i)
    val (ur, p) = context.get(id)
    val unit    = ur.get

    val program = unit.program
    val ctx     = unit.ctx

    ctx.reporter.debug("Executing SAT problem (codegen)!")
    val is = inputs.toSeq

    if (!cache.containsKey(id)) {
      cache.put(id, new MutableMap())
    }

    val resultCache = cache.get(id)

    if (resultCache contains is) {
      resultCache(is).isDefined
    } else {
      val tStart = System.currentTimeMillis

      val solverf = SolverFactory.default(ctx, program).withTimeout(10.second)
      val solver = solverf.getNewSolver()

      val bindingCnstrs = (p.args zip inputs).flatMap { case (id, jvmExpr) =>
        val v = Variable(id)
        val expr = unit.jvmToExpr(jvmExpr, id.getType)

        val inputCnstr = expr match {
          case purescala.Extractors.FiniteLambda(default, mapping) =>
            Some(ElementOfSet(v, FiniteSet(mapping.map(_._1).toSet, id.getType)))
          case _ => None
        }

        Seq(Equals(v, expr)) ++ inputCnstr
      }

      solver.assertCnstr(andJoin(p.problem +: bindingCnstrs))

      try {
        solver.check match {
          case Some(true) =>
            val model = solver.getModel
            val valModel = valuateWithModel(model) _
            val res = p.args.map(valModel)
            val leonRes = tupleWrap(res)

            val total = System.currentTimeMillis-tStart

            ctx.reporter.debug("Constraint \"execution\" took "+total+"ms")
            ctx.reporter.debug("SAT with model "+leonRes.asString(ctx))

            val obj = unit.exprToJVM(leonRes)(new LeonCodeGenRuntimeMonitor(unit.params.maxFunctionInvocations))
            resultCache += is -> Some(obj)
            true

          case Some(false) =>
            resultCache += is -> None
            false

          case _ =>
            throw new LeonCodeGenRuntimeException("Timeout exceeded")
        }
      } finally {
        solver.free()
        solverf.shutdown()
      }
    }
  }

  def getModel(i: Int, inputs: Array[AnyRef]): java.lang.Object = {
    val id = ExprId(i)
    if (!cache.containsKey(id)) {
      throw new LeonCodeGenRuntimeException("Problem was not checked before model query")
    }

    cache.get(id).get(inputs.toSeq) match {
      case Some(Some(obj)) =>
        obj
      case Some(None) =>
        throw new LeonCodeGenRuntimeException("Problem was UNSAT")
      case None =>
        throw new LeonCodeGenRuntimeException("Problem was not checked before model query")
    }
  }
}

