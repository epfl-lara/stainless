/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package evaluators

import codegen._
import runtime._

import inox.utils.UniqueCounter

import cafebabe._
import cafebabe.AbstractByteCodes._
import cafebabe.ByteCodes._
import cafebabe.ClassFileTypes._
import cafebabe.Flags._

import scala.collection.JavaConverters._

import java.lang.reflect.Constructor

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

  class Monitor(maxCalls: Int) extends runtime.Monitor {
    private[this] var calls = 0

    def onInvocation(): Unit = {
      if (maxCalls >= 0) {
        if (calls < maxCalls) {
          calls += 1
        } else {
          throw new CodeGenRuntimeException(s"Maximum number of invocations reached ($maxCalls).")
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

}
