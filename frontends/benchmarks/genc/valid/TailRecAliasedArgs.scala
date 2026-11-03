import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecAliasedArgs {
  def aliased(n: Int, a: Int, b: Int): Int =
    // The values at most double at each step, so they cannot overflow in the remaining n steps
    require(0 <= n && n <= 30 && 0 <= a && a <= (1 << (30 - n)) && 0 <= b && b <= (1 << (30 - n)))
    decreases(n)
    if n == 0 then a
    else aliased(n - 1, b, a + b)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(aliased(5, 0, 1)) // Expected: 5
  }
}
