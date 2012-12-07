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

  def eval(args: Seq[Expr]): Expr = {
    val cl = unit.loader.loadClass(cf.className)
    val obj = cl.newInstance()
    val meth = cl.getMethods()(0)

    val res = meth.invoke(obj, args.map(unit.groundExprToJava))

    unit.javaToGroundExpr(res)
  }

} 
