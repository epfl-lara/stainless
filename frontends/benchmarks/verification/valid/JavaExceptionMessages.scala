// The package keeps the top-level `IllegalArgumentException` of the `Throw` benchmark out of scope, and only
// the decorations are imported, so that the names of exceptions refer to the Java ones
package javaexceptionmessages

import stainless.lang.BooleanDecorations

// The messages of Java exceptions are the ones given to their constructors.
object JavaExceptionMessages {
  case class FatalError(msg: String) extends Exception(msg)
  class Unsupported extends UnsupportedOperationException("unsupported")
  class SolverError(msg: String) extends Exception(msg)
  case class Timeout(limit: BigInt) extends SolverError("timeout")

  def message(x: BigInt): String = {
    try {
      if (x == 0) throw new IllegalArgumentException("zero")
      "none"
    } catch {
      case e: IllegalArgumentException => e.getMessage
    }
  }.ensuring(res => x == 0 ==> (res == "zero"))

  def messages(s: String): Boolean = {
    FatalError("fatal").getMessage == "fatal" &&
    (new Unsupported).getMessage == "unsupported" &&
    new RuntimeException().getMessage == "" &&
    new IllegalStateException("state: " + s).getMessage == "state: " + s
  }.holds

  def timeoutMessage(): Boolean = { Timeout(3).getMessage == "timeout" }.holds
}
