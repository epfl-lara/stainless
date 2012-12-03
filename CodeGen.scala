package leon
package codegen

import purescala.Common._
import purescala.Definitions._

object CodeGenPhase extends LeonPhase[Program,CompilationResult] {
  val name = "CodeGen"
  val description = "Compiles a Leon program into Java methods"

  def run(ctx : LeonContext)(p : Program) : CompilationResult = {
    CompilationResult(successful = true)
  } 
}
