import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecAliasedArgs {
  def aliased(n: Int, a: Int, b: Int): Int =
    require(n >= 0)
    decreases(n)
    if n == 0 then a
    else aliased(n - 1, b, a + b)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(aliased(5, 0, 1)) // Expected: 5
  }
}
