import stainless.annotation._
import stainless.lang._

object TailRecReturnInLoop {

  def fib(n: Int, i: Int = 0, j: Int = 1): Int =
    while (true) {
        if n == 0 then return i
        else return fib(n-1, j, i+j)
    }
    1

  @cCode.`export`
  def main(): Int = {
    implicit val state = stainless.io.newState
    fib(10)
  }

}
