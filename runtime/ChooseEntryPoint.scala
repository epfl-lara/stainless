/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package codegen.runtime

import utils._
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

object ChooseEntryPoint {
  implicit val debugSection = DebugSectionSynthesis

  private case class ChooseId(id: Int) { }

  private[this] val context = new WeakHashMap[ChooseId, (WeakReference[CompilationUnit], Problem)]()
  private[this] val cache   = new WeakHashMap[ChooseId, MutableMap[Seq[AnyRef], java.lang.Object]]()

  private[this] val ids = new WeakHashMap[CompilationUnit, MutableMap[Problem, ChooseId]]()

  private val intCounter = new UniqueCounter[Unit]
  intCounter.nextGlobal // Start with 1

  private def getUniqueId(unit: CompilationUnit, p: Problem): ChooseId = synchronized {
    if (!ids.containsKey(unit)) {
      ids.put(unit, new MutableMap())
    }

    if (ids.get(unit) contains p) {
      ids.get(unit)(p)
    } else {
      val cid = new ChooseId(intCounter.nextGlobal)
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

      val solverf = SolverFactory.default(ctx, program).withTimeout(10.second)
      val solver = solverf.getNewSolver()

      val inputsMap = (p.as zip inputs).map {
        case (id, v) =>
          Equals(Variable(id), unit.jvmToValue(v, id.getType))
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

            val obj = unit.valueToJVM(leonRes)(new LeonCodeGenRuntimeMonitor(unit.params.maxFunctionInvocations))
            chCache += is -> obj
            obj
          case Some(false) =>
            throw new LeonCodeGenRuntimeException("Constraint is UNSAT")
          case _ =>
            throw new LeonCodeGenRuntimeException("Timeout exceeded")
        }
      } finally {
        solver.free()
        solverf.shutdown()
      }
    }
  }
}
