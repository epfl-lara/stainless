import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecEarlyReturn {
  def earlyReturn(n: Int, acc: Int): Int =
    if n == 0 then acc
    else if n == 3 then return acc * 2 // Early return
    else earlyReturn(n - 1, acc + 1)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(earlyReturn(5, 0)) // Expected: 4
  }
}
