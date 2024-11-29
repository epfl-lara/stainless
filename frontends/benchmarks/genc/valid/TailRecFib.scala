import stainless.annotation._
import stainless.lang._

object TailRecFib {

  def fib(n: Int, i: Int = 0, j: Int = 1): Int =
    if n == 0 then i
    else fib(n-1, j, i+j)

  @cCode.`export`
  def main(): Int = {
    implicit val state = stainless.io.newState
    fib(10)
  }

}
