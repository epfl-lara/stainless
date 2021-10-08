/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package evaluators

import codegen._

import inox.utils.UniqueCounter

import cafebabe._
import cafebabe.AbstractByteCodes._
import cafebabe.ByteCodes._
import cafebabe.ClassFileTypes._
import cafebabe.Flags._

import java.lang.reflect.Constructor

import inox.evaluators._
import evaluators._

import scala.util.Try
import scala.collection.JavaConverters._
import scala.collection.mutable.{Map => MutableMap}

class CodeGenEvaluator(override val program: Program,
                       override val context: inox.Context)
                      (using override val semantics: program.Semantics)
  extends CompilationUnit(program, context)
     with inox.evaluators.DeterministicEvaluator
     with inox.evaluators.SolvingEvaluator { self =>

  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  class Monitor(model: program.Model) extends runtime.Monitor {
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
      static.map(tpe => registerType(typeOps.instantiateType(tpe, tpMap))).toArray
    }

    def typeSubstitute(id: Int, closures: Array[AnyRef]): Int = {
      val tpe = getType(id)

      val vars = typeOps.variablesOf(tpe)
      val subst = (vars.toSeq.sortBy(_.id) zip closures.toSeq).map {
        case (v, ref) => v -> jvmToValue(ref, v.getType)
      }.toMap

      val newType = typeOps.replaceFromSymbols(subst, tpe)
      registerType(newType)
    }

    def onChooseInvocation(id: Int, tps: Array[Int], inputs: Array[AnyRef]): AnyRef = {
      val (params, tparams, choose) = getChoose(id)

      val newTypes = tps.toSeq.map(getType)
      val tpMap = (tparams zip newTypes).toMap

      val tpChoose = typeOps.instantiateType(choose, tpMap)

      val realParams = params.map { vd =>
        vd.copy(tpe = typeOps.instantiateType(vd.tpe, tpMap))
      }

      val inputsMap = (realParams zip inputs.toSeq).map {
        case (vd, ref) => vd.toVariable -> jvmToValue(ref, vd.getType)
      }.toMap

      val res = model.chooses.get(choose.res.id -> newTypes) match {
        case Some(value) =>
          val vars = inputsMap map { case (k, v) => k.toVal -> v }
          val subModel = inox.Model(model.program)(vars, model.chooses)

          eval(value, subModel) match {
            case EvaluationResults.Successful(result) =>
              result
            case EvaluationResults.RuntimeError(msg) =>
              throw new runtime.CodeGenRuntimeException(msg)
            case EvaluationResults.EvaluatorError(msg) =>
              throw new runtime.CodeGenRuntimeException(msg)
          }

        case None =>
          val groundChoose = exprOps.replaceFromSymbols(inputsMap, tpChoose)
          try {
            self.onChooseInvocation(groundChoose.asInstanceOf[Choose])
          } catch {
            case e: java.lang.RuntimeException =>
              throw new runtime.CodeGenRuntimeException(e.getMessage)
          }
      }


      valueToJVM(res)(using this)
    }

    def onForallInvocation(id: Int, tps: Array[Int], inputs: Array[AnyRef]): Boolean = {
      val (tparams, forall) = getForall(id)

      val newTypes = tps.toSeq.map(getType)
      val tpMap = (tparams zip newTypes).toMap

      val tpForall = typeOps.instantiateType(forall, tpMap)
      val vars = exprOps.variablesOf(tpForall).toSeq.sortBy(_.id.uniqueName)

      val inputsMap = (vars zip inputs.toSeq).map {
        case (v, ref) => v -> jvmToValue(ref, v.getType)
      }.toMap

      val groundForall = exprOps.replaceFromSymbols(inputsMap, tpForall)

      val BooleanLiteral(res) = try {
        self.onForallInvocation(groundForall.asInstanceOf[Forall])
      } catch {
        case e: java.lang.RuntimeException =>
          throw new runtime.CodeGenRuntimeException(e.getMessage)
      }

      res
    }
  }

  def eval(expr: Expr, model: program.Model) = {
    compile(expr, model.vars.toSeq.map(_._1)).map { e =>
      timers.evaluators.codegen.runtime.run { e(model) }
    }.getOrElse(EvaluationResults.EvaluatorError(s"Couldn't compile expression: $expr"))
  }

  private def compileExpr(expr: Expr, args: Seq[ValDef]): Try[CompiledExpression] =
    timers.evaluators.codegen.compilation.run { Try(compileExpression(expr, args)) }

  override def compile(expr: Expr, args: Seq[ValDef]) = {
    compileExpr(expr, args).map(ce => (model: program.Model) => {
      if (args.exists(arg => !model.vars.isDefinedAt(arg))) {
        EvaluationResults.EvaluatorError("Model undefined for free arguments")
      } else try {
        EvaluationResults.Successful(ce.eval(model)(new Monitor(model)))
      } catch {
        case e: ArithmeticException =>
          EvaluationResults.RuntimeError(e.getMessage)

        case e: ArrayIndexOutOfBoundsException =>
          EvaluationResults.RuntimeError(e.getMessage)

        case e: runtime.CodeGenRuntimeException =>
          EvaluationResults.RuntimeError(e.getMessage)

        case e: java.lang.ClassCastException =>
          EvaluationResults.RuntimeError(e.getMessage)

        case e: java.lang.ExceptionInInitializerError =>
          EvaluationResults.RuntimeError(e.getException.getMessage)

        case e: java.lang.StackOverflowError =>
          EvaluationResults.RuntimeError("Stack overflow")

        case e: java.lang.OutOfMemoryError =>
          EvaluationResults.RuntimeError("Out of memory")
      }
    }).recover {
      case t: Throwable =>
        (model: program.Model) => EvaluationResults.EvaluatorError(t.getMessage)
    }.toOption
  }
}

object CodeGenEvaluator {
  def apply(p: StainlessProgram, ctx: inox.Context): DeterministicEvaluator { val program: p.type } = {
    val split = FunctionSplitting(p, size = 5000, slots = 100)
    class Impl(override val program: split.targetProgram.type)
      extends CodeGenEvaluator(program, ctx)(using split.targetProgram.getSemantics)

    EncodingEvaluator(p)(split)(new Impl(split.targetProgram))
  }
}
