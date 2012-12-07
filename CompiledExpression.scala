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

class CompiledExpression(unit: CompilationUnit, cf: ClassFile, argsDecl: Seq[Identifier]) {

  def evalToJava(args: Seq[Expr]): AnyRef = {
    val cl = unit.loader.loadClass(cf.className)
    val meth = cl.getMethods()(0)

    assert(args.size == argsDecl.size)

    if (args.isEmpty) {
      meth.invoke(null)
    } else {
      meth.invoke(null, args.map(unit.groundExprToJava).toArray)
    }
  }

  def eval(args: Seq[Expr]): Expr = {
    unit.javaToGroundExpr(evalToJava(args))
  }

} 
