import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecMutualRecursion {
  def even(n: Int): Int =
    if n == 0 then 1
    else odd(n - 1)

  def odd(n: Int): Int =
    if n == 0 then 0
    else even(n - 1)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(even(10)) // Expected: 1
  }
}
