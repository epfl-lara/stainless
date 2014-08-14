/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package codegen.runtime

import utils._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees.{Tuple => LeonTuple, _}
import purescala.TreeOps.valuateWithModel
import purescala.TypeTrees._
import solvers.TimeoutSolver
import solvers.z3._

import codegen.CompilationUnit

import scala.collection.immutable.{Map => ScalaMap}

import synthesis._

object ChooseEntryPoint {
  private[this] var map = ScalaMap[Int, (Problem, CompilationUnit)]()

  implicit val debugSection = DebugSectionSynthesis

  def register(p: Problem, unit: CompilationUnit): Int = {
    val stored = (p, unit)
    val hash = stored.##

    map += hash -> stored

    hash
  }

  def invoke(i: Int, inputs: Array[AnyRef]): java.lang.Object = {
    val (p, unit) = map(i)

    val program = unit.program
    val ctx     = unit.ctx

    ctx.reporter.debug("Executing choose!")

    val tStart = System.currentTimeMillis;

    val solver = (new FairZ3Solver(ctx, program) with TimeoutSolver).setTimeout(10000L)

    val inputsMap = (p.as zip inputs).map {
      case (id, v) =>
        Equals(Variable(id), unit.jvmToExpr(v, id.getType))
    }

    solver.assertCnstr(And(Seq(p.pc, p.phi) ++ inputsMap))

    try {
      solver.check match {
        case Some(true) =>
          val model = solver.getModel;

          val valModel = valuateWithModel(model) _

          val res = p.xs.map(valModel)
          val leonRes = if (res.size > 1) {
            LeonTuple(res)
          } else {
            res(0)
          }

          val total = System.currentTimeMillis-tStart;

          ctx.reporter.debug("Synthesis took "+total+"ms")
          ctx.reporter.debug("Finished synthesis with "+leonRes.asString(ctx))

          unit.exprToJVM(leonRes)(new LeonCodeGenRuntimeMonitor(unit.params.maxFunctionInvocations))
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
