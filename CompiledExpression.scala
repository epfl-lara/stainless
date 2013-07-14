/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package codegen

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

import cafebabe._
import cafebabe.AbstractByteCodes._
import cafebabe.ByteCodes._
import cafebabe.ClassFileTypes._
import cafebabe.Flags._

import java.lang.reflect.InvocationTargetException

class CompiledExpression(unit: CompilationUnit, cf: ClassFile, expression : Expr, argsDecl: Seq[Identifier]) {
  private lazy val cl = unit.loader.loadClass(cf.className)
  private lazy val meth = cl.getMethods()(0)

  private val exprType = expression.getType

  def argsToJVM(args: Seq[Expr]): Seq[AnyRef] = {
    args.map(unit.valueToJVM)
  }

  def evalToJVM(args: Seq[AnyRef]): AnyRef = {
    assert(args.size == argsDecl.size)

    if (args.isEmpty) {
      meth.invoke(null)
    } else {
      meth.invoke(null, args.toArray : _*)
    }
  }

  // This may throw an exception. We unwrap it if needed.
  // We also need to reattach a type in some cases (sets, maps).
  def evalFromJVM(args: Seq[AnyRef]) : Expr = {
    try {
      val result = unit.jvmToValue(evalToJVM(args))
      if(!result.isTyped) {
        result.setType(exprType)
      }
      result
    } catch {
      case ite : InvocationTargetException => throw ite.getCause()
    }
  }

  def eval(args: Seq[Expr]) : Expr = {
    try {
      evalFromJVM(argsToJVM(args))
    } catch {
      case ite : InvocationTargetException => throw ite.getCause()
    }
  }
} 
