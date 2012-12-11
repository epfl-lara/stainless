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

  protected[codegen] def evalToJVM(args: Seq[Expr]): AnyRef = {
    assert(args.size == argsDecl.size)

    if (args.isEmpty) {
      meth.invoke(null)
    } else {
      meth.invoke(null, args.map(unit.valueToJVM).toArray : _*)
    }
  }

  // This may throw an exception. We unwrap it if needed.
  def eval(args: Seq[Expr]) : Expr = {
    try {
      unit.jvmToValue(evalToJVM(args))
    } catch {
      case ite : InvocationTargetException => throw ite.getCause()
    }
  }
} 
