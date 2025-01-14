import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecFibAliased {

  def fib(n: Int, i: Int = 0, j: Int = 1): Int =
    require(n >= 0)
    decreases(n)
    if n == 0 then i
    else
        val res = fib(n-1, j, i+j)
        res

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(fib(10))
  }

}
