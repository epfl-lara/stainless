package functionClosure2
import language.experimental.qualifiedTypes.silent
import stainless.lang._

object FunctionClosure2:
  def foo(a: Array[BigInt]) =
    val N = a.length
    var (j : Int with j >= 0 && j <= N) = 0
    while (j < N) {
      decreases(N - j)
      j = j + 1
    }
