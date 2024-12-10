import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecMutualRecursion {
  def even(n: Int): Boolean =
    if n == 0 then true
    else odd(n - 1)

  def odd(n: Int): Boolean =
    if n == 0 then false
    else even(n - 1)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(even(10)) // Expected: true
  }
}
