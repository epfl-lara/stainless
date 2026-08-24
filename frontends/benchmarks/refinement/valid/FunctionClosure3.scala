package functionClosure3
import stainless.lang._

object FunctionClosure3:
  def foo() =
    val x = 1
    val y = x + 3
    def bar(): Int = y
