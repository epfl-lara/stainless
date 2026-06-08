package functionClosure4
import language.experimental.qualifiedTypes.silent
import stainless.lang._

object FunctionClosure4:
  def foo() =
    val x = 1
    val y = x + 3
    def bar(): Int = 
      def baz(): Int = y
      baz() + y
