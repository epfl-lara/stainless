package functionClosure5
import stainless.lang._

object FunctionClosure5:
  def bar(i: Int, arr: Array[Int]) =
    require(i >= 0 && i < arr.length)
    val c = arr(i)
    def foo() = c