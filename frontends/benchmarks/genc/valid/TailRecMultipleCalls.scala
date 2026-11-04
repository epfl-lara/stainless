import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecMultipleCalls {
  def multipleCalls(n: Int, acc: Int): Int =
    // `acc` grows by at most 2 per step
    require(0 <= n && n <= 1000 && 0 <= acc && acc <= 1000 - 2 * n)
    decreases(n)
    if n == 0 then acc
    else if n == 1 then acc + 2
    else if n % 2 == 0 then multipleCalls(n - 1, acc + 1)
    else multipleCalls(n - 2, acc + 2)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(multipleCalls(10, 0)) // Expected: 11
  }
}
