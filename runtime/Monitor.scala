/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package codegen.runtime

import utils._
import purescala.Expressions._
import purescala.Constructors._
import purescala.Common._
import purescala.ExprOps.valuateWithModel

import codegen.CompilationUnit

import scala.collection.immutable.{Map => ScalaMap}
import scala.collection.mutable.{HashMap => MutableMap}
import scala.concurrent.duration._

import solvers.SolverFactory


import synthesis._

abstract class Monitor {
  def onInvocation(): Unit

  def onAbstractInvocation(id: Int, args: Array[AnyRef]): AnyRef

  def onChooseInvocation(id: Int, args: Array[AnyRef]): AnyRef
}

class NoMonitor extends Monitor {
  def onInvocation(): Unit = {}

  def onAbstractInvocation(id: Int, args: Array[AnyRef]): AnyRef = {
    throw new LeonCodeGenEvaluationException("No monitor available.");
  }

  def onChooseInvocation(id: Int, args: Array[AnyRef]): AnyRef = {
    throw new LeonCodeGenEvaluationException("No monitor available.");
  }
}

class StdMonitor(unit: CompilationUnit, invocationsMax: Int, bodies: ScalaMap[Identifier, Expr]) extends Monitor {

  private[this] var invocations = 0

  def onInvocation(): Unit = {
    if(invocationsMax >= 0) {
      if (invocations < invocationsMax) {
        invocations += 1;
      } else {
        throw new LeonCodeGenEvaluationException("Maximum number of invocations reached ("+invocationsMax+").");
      }
    }
  }

  def onAbstractInvocation(id: Int, args: Array[AnyRef]): AnyRef = {
    val fd = unit.runtimeAbstractMap(id)

    bodies.get(fd.id) match {
      case Some(expr) =>
        throw new LeonCodeGenRuntimeException("Found body!")

      case None =>
        throw new LeonCodeGenRuntimeException("Did not find body!")
    }
  }


  private[this] val cache   = new MutableMap[(Int, Seq[AnyRef]), AnyRef]()

  def onChooseInvocation(id: Int, inputs: Array[AnyRef]): AnyRef = {

    implicit val debugSection = DebugSectionSynthesis

    val p = unit.runtimeProblemMap(id)

    val program = unit.program
    val ctx     = unit.ctx

    ctx.reporter.debug("Executing choose (codegen)!")
    val is = inputs.toSeq

    if (cache contains ((id, is))) {
      cache((id, is))
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

            val obj = unit.valueToJVM(leonRes)(this)
            cache += (id, is) -> obj
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

