/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package evaluators

import codegen._

import inox.utils.UniqueCounter

import cafebabe._
import cafebabe.AbstractByteCodes._
import cafebabe.ByteCodes._
import cafebabe.ClassFileTypes._
import cafebabe.Flags._

import scala.collection.JavaConverters._

import java.lang.reflect.Constructor

import inox.evaluators._
import evaluators._

import scala.collection.mutable.{Map => MutableMap}

trait CodeGenEvaluator
  extends CompilationUnit
     with inox.evaluators.DeterministicEvaluator
     with inox.evaluators.SolvingEvaluator { self =>

  val program: Program

  import program._
  import program.trees._
  import program.symbols._

  class Monitor extends runtime.Monitor {
    private[this] var calls = 0

    def onInvocation(): Unit = {
      if (maxSteps >= 0) {
        if (calls < maxSteps) {
          calls += 1
        } else {
          throw new runtime.CodeGenRuntimeException(s"Maximum number of invocations reached ($maxSteps).")
        }
      }
    }

    def typeParams(params: Array[Int], tps: Array[Int], newTps: Array[Int]): Array[Int] = {
      val tparams = params.toSeq.map(getType(_).asInstanceOf[TypeParameter])
      val static = tps.toSeq.map(getType)
      val newTypes = newTps.toSeq.map(getType)
      val tpMap = (tparams zip newTypes).toMap
      static.map(tpe => registerType(instantiateType(tpe, tpMap))).toArray
    }

    def onChooseInvocation(id: Int, tps: Array[Int], inputs: Array[AnyRef]): AnyRef = {
      //ctx.reporter.debug("Executing choose (codegen)")

      val (tparams, choose) = getChoose(id)

      val newTypes = tps.toSeq.map(getType)
      val tpMap = (tparams zip newTypes).toMap

      val tpChoose = instantiateType(choose, tpMap)
      val vars = exprOps.variablesOf(tpChoose).toSeq.sortBy(_.id.uniqueName)

      val inputsMap = (vars zip inputs.toSeq).map {
        case (v, ref) => v -> jvmToValue(ref, v.tpe)
      }.toMap

      val groundChoose = exprOps.replaceFromSymbols(inputsMap, tpChoose)
      val res = self.onChooseInvocation(groundChoose.asInstanceOf[Choose])
      valueToJVM(res)(this)
    }

    def onForallInvocation(id: Int, tps: Array[Int], inputs: Array[AnyRef]): Boolean = {
      //ctx.reporter.debug("Executing forall (codegen)")

      val (tparams, forall) = getForall(id)

      val newTypes = tps.toSeq.map(getType)
      val tpMap = (tparams zip newTypes).toMap

      val tpForall = instantiateType(forall, tpMap)
      val vars = exprOps.variablesOf(tpForall).toSeq.sortBy(_.id.uniqueName)

      val inputsMap = (vars zip inputs.toSeq).map {
        case (v, ref) => v -> jvmToValue(ref, v.tpe)
      }.toMap

      val groundForall = exprOps.replaceFromSymbols(inputsMap, tpForall)
      val BooleanLiteral(res) = self.onForallInvocation(groundForall.asInstanceOf[Forall])
      res
    }
  }

  def eval(expr: Expr, model: Map[ValDef, Expr]) = {
    compile(expr, model.toSeq.map(_._1)).map { e =>
      val timer = ctx.timers.evaluators.codegen.runtime.start()
      val res = e(model)
      timer.stop()
      res
    }.getOrElse(EvaluationResults.EvaluatorError("Couldn't compile expression"))
  }

  private def compileExpr(expr: Expr, args: Seq[ValDef]): Option[CompiledExpression] = {
    val timer = ctx.timers.evaluators.codegen.compilation.start()
    try {
      Some(compileExpression(expr, args))
    } catch {
      case t: Throwable =>
        ctx.reporter.warning(expr.getPos, "Error while compiling expression: " + t.getMessage)
        None
    } finally {
      timer.stop()
    }
  }

  override def compile(expr: Expr, args: Seq[ValDef]) = {
    compileExpr(expr, args).map(ce => (model: Map[ValDef, Expr]) => {
      if (args.exists(arg => !model.isDefinedAt(arg))) {
        EvaluationResults.EvaluatorError("Model undefined for free arguments")
      } else try {
        EvaluationResults.Successful(ce.eval(model)(new Monitor))
      } catch {
        case e: ArithmeticException =>
          EvaluationResults.RuntimeError(e.getMessage)

        case e: ArrayIndexOutOfBoundsException =>
          EvaluationResults.RuntimeError(e.getMessage)

        case e: runtime.CodeGenRuntimeException =>
          EvaluationResults.RuntimeError(e.getMessage)

        case e: java.lang.ExceptionInInitializerError =>
          EvaluationResults.RuntimeError(e.getException.getMessage)

        case e: java.lang.StackOverflowError =>
          EvaluationResults.RuntimeError("Stack overflow")
      }
    })
  }
}

object CodeGenEvaluator {
  def apply(p: StainlessProgram, opts: inox.Options): CodeGenEvaluator { val program: p.type } = {
    new {
      val program: p.type = p
      val options = opts
    } with CodeGenEvaluator {
      def getSolver(moreOpts: inox.OptionValue[_]*) = solvers.SolverFactory(p, opts ++ moreOpts)
    }
  }

  def default(p: StainlessProgram) = apply(p, p.ctx.options)
}
