import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecNoArguments {
  def countDown(n: Int): Int =
    if n == 0 then 0
    else countDown(n - 1)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(countDown(1000000)) // Expected: 0
  }
}
