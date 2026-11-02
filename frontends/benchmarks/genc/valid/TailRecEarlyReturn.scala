import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecEarlyReturn {
  def earlyReturn(n: Int, acc: Int): Int =
    // `acc` grows by 1 per step, and is doubled at most once
    require(0 <= n && n <= 1000 && 0 <= acc && acc <= 1000 - n)
    decreases(n)
    if n == 0 then acc
    else if n == 3 then return acc * 2 // Early return
    else earlyReturn(n - 1, acc + 1)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(earlyReturn(5, 0)) // Expected: 4
  }
}
