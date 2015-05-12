/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package codegen

import purescala.Common._
import purescala.Expressions._

import cafebabe._

import runtime.{LeonCodeGenRuntimeMonitor => LM, LeonCodeGenRuntimeHenkinMonitor => LHM}

import java.lang.reflect.InvocationTargetException

class CompiledExpression(unit: CompilationUnit, cf: ClassFile, expression: Expr, argsDecl: Seq[Identifier]) {

  private lazy val cl = unit.loader.loadClass(cf.className)
  private lazy val meth = cl.getMethods()(0)

  private val exprType = expression.getType

  private val params = unit.params

  def argsToJVM(args: Seq[Expr], monitor: LM): Seq[AnyRef] = {
    args.map(unit.valueToJVM(_)(monitor))
  }

  def evalToJVM(args: Seq[AnyRef], monitor: LM): AnyRef = {
    assert(args.size == argsDecl.size)

    val realArgs = if (unit.requireMonitor) {
      monitor +: args
    } else {
      args
    }

    if (realArgs.isEmpty) {
      meth.invoke(null)
    } else {
      meth.invoke(null, realArgs.toArray : _*)
    }
  }

  // This may throw an exception. We unwrap it if needed.
  // We also need to reattach a type in some cases (sets, maps).
  def evalFromJVM(args: Seq[AnyRef], monitor: LM) : Expr = {
    try {
      unit.jvmToValue(evalToJVM(args, monitor), exprType)
    } catch {
      case ite : InvocationTargetException => throw ite.getCause
    }
  }

  def eval(model: solvers.Model) : Expr = {
    try {
      val monitor = unit.modelToJVM(model, params.maxFunctionInvocations)
      evalFromJVM(argsToJVM(argsDecl.map(model), monitor), monitor)
    } catch {
      case ite : InvocationTargetException => throw ite.getCause
    }
  }
}
