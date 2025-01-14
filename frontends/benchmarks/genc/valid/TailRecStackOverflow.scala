import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecStackOverflow {
  def even(n: Int): Int =
    require(n >= 0)
    decreases(n)
    if n == 0 then 1
    else if n == 1 then 0
    else even(n - 2)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(even(1000000)) // Expected: 1
  }
}
