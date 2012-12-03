package leon
package codegen

import purescala.Common._
import purescala.Definitions._

abstract class CompilationEnvironment() {
  // Should contain:
  //   - a mapping of function defs to class + method name
  //   - a mapping of class defs to class names
  //   - a mapping of class fields to fields

  def funDefToMethod(funDef : FunDef) : Option[(String,String)]
}

object CompilationEnvironment {
  def fromProgram(p : Program) : CompilationEnvironment = {
    val className = CodeGeneration.programToClassName(p)

    val fs = p.definedFunctions.filter(_.hasImplementation)
    val fPairs : Map[FunDef,String] = fs.map(fd => (fd -> fd.id.uniqueName)).toMap

    new CompilationEnvironment {
      def funDefToMethod(funDef : FunDef) = fPairs.get(funDef).map(n => (className, n))
    }
  }
}
