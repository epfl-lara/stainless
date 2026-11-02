import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecFib {

  def fib(n: Int, i: Int = 0, j: Int = 1): Int =
    // The values at most double at each step, so they cannot overflow in the remaining n steps
    require(0 <= n && n <= 30 && 0 <= i && i <= (1 << (30 - n)) && 0 <= j && j <= (1 << (30 - n)))
    decreases(n)
    if n == 0 then i
    else fib(n-1, j, i+j)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(fib(10))
  }

}
