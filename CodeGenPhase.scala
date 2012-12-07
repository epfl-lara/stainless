package leon
package codegen

import purescala.Common._
import purescala.Definitions._

import cafebabe._
import cafebabe.ClassFileTypes.U2
import cafebabe.Flags._

object CodeGenPhase extends LeonPhase[Program,CompilationResult] {
  val name = "CodeGen"
  val description = "Compiles a Leon program into Java methods"

  def run(ctx : LeonContext)(p : Program) : CompilationResult = {
    import CodeGeneration._

    CompilationUnit.compileProgram(p) match {
      case Some(unit) => 
        unit.writeClassFiles()
        CompilationResult(successful = true)
      case None =>
        CompilationResult(successful = false)
    }

  } 
}
