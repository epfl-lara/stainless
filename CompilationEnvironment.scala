package leon
package codegen

import purescala.Common._
import purescala.Definitions._

abstract class CompilationEnvironment() {
  self =>
  // Should contain:
  //   - a mapping of function defs to class + method name
  //   - a mapping of class defs to class names
  //   - a mapping of class fields to fields

  def funDefToMethod(funDef : FunDef) : Option[(String,String,String)]

  def varToLocal(v : Identifier) : Option[Int]

  /** Augment the environment with new local var. mappings. */
  def withVars(pairs : Map[Identifier,Int]) = {
    new CompilationEnvironment {
      def funDefToMethod(funDef : FunDef) = self.funDefToMethod(funDef)
      def varToLocal(v : Identifier) = pairs.get(v).orElse(self.varToLocal(v))
    }
  }
}

object CompilationEnvironment {

  lazy val empty = new CompilationEnvironment {
    def funDefToMethod(funDef : FunDef) = None
    def varToLocal(v : Identifier) = None
  }

  def fromProgram(p : Program) : CompilationEnvironment = {
    import CodeGeneration.typeToJVM

    // This should change: it should contain the case classes before
    // we go and generate function signatures.
    implicit val env = empty

    val className = CodeGeneration.programToClassName(p)

    val fs = p.definedFunctions.filter(_.hasImplementation)

    val fMap : Map[FunDef,(String,String,String)] = (fs.map { fd =>
      val sig = "(" + fd.args.map(a => typeToJVM(a.tpe)).mkString("") + ")" + typeToJVM(fd.returnType)

      fd -> (className, fd.id.uniqueName, sig)
    }).toMap

    new CompilationEnvironment {
      def funDefToMethod(funDef : FunDef) = fMap.get(funDef)

      def varToLocal(v : Identifier) = None
    }
  }
}
