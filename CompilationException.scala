package leon
package codegen

case class CompilationException(msg : String) extends Exception {
  override def getMessage = msg
}
