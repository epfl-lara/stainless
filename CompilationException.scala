/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package codegen

case class CompilationException(msg : String) extends Exception {
  override def getMessage = msg
}
