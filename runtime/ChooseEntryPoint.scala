/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package codegen.runtime

import utils._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions.{Tuple => LeonTuple, _}
import purescala.ExprOps.valuateWithModel
import purescala.Types._
import purescala.Constructors._
import solvers.TimeoutSolver
import solvers.z3._

import java.util.WeakHashMap
import java.lang.ref.WeakReference
import scala.collection.mutable.{HashMap => MutableMap}

import codegen.CompilationUnit

import synthesis._

object ChooseEntryPoint {
  implicit val debugSection = DebugSectionSynthesis

  private case class ChooseId(id: Int) { }

  private[this] val context = new WeakHashMap[ChooseId, (WeakReference[CompilationUnit], Problem)]()
  private[this] val cache   = new WeakHashMap[ChooseId, MutableMap[Seq[AnyRef], java.lang.Object]]()

  private[this] val ids = new WeakHashMap[CompilationUnit, MutableMap[Problem, ChooseId]]()

  private[this] var _next = 0
  private[this] def nextInt(): Int = {
    _next += 1
    _next
  }

  private def getUniqueId(unit: CompilationUnit, p: Problem): ChooseId = {
    if (!ids.containsKey(unit)) {
      ids.put(unit, new MutableMap())
    }

    if (ids.get(unit) contains p) {
      ids.get(unit)(p)
    } else {
      val cid = new ChooseId(nextInt())
      ids.get(unit) += p -> cid
      cid
    }
  }


  def register(p: Problem, unit: CompilationUnit): Int = {
    val cid = getUniqueId(unit, p)

    context.put(cid, new WeakReference(unit) -> p)

    cid.id
  }

  def invoke(i: Int, inputs: Array[AnyRef]): java.lang.Object = {
    val id = ChooseId(i)
    val (ur, p) = context.get(id)
    val unit    = ur.get

    val program = unit.program
    val ctx     = unit.ctx

    ctx.reporter.debug("Executing choose (codegen)!")
    val is = inputs.toSeq

    if (!cache.containsKey(id)) {
      cache.put(id, new MutableMap())
    }

    val chCache = cache.get(id)

    if (chCache contains is) {
      chCache(is)
    } else {
      val tStart = System.currentTimeMillis

      val solver = (new FairZ3Solver(ctx, program) with TimeoutSolver).setTimeout(10000L)

      val inputsMap = (p.as zip inputs).map {
        case (id, v) =>
          Equals(Variable(id), unit.jvmToExpr(v, id.getType))
      }

      solver.assertCnstr(andJoin(Seq(p.pc, p.phi) ++ inputsMap))

      try {
        solver.check match {
          case Some(true) =>
            val model = solver.getModel

            val valModel = valuateWithModel(model) _

            val res = p.xs.map(valModel)
            val leonRes = tupleWrap(res) 

            val total = System.currentTimeMillis-tStart

            ctx.reporter.debug("Synthesis took "+total+"ms")
            ctx.reporter.debug("Finished synthesis with "+leonRes.asString(ctx))

            val obj = unit.exprToJVM(leonRes)(new LeonCodeGenRuntimeMonitor(unit.params.maxFunctionInvocations))
            chCache += is -> obj
            obj
          case Some(false) =>
            throw new LeonCodeGenRuntimeException("Constraint is UNSAT")
          case _ =>
            throw new LeonCodeGenRuntimeException("Timeout exceeded")
        }
      } finally {
        solver.free()
      }
    }
  }
}
