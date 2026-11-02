import stainless.annotation._
import stainless.lang._
import stainless.io._

/**
 * Assignments to ghost fields and ghost local variables outside of `ghost` blocks
 * are erased together with the ghost state they write to.
 */
object GhostAssignments {

  case class Counter(var n: Int, var last: Int, @ghost var count: BigInt)

  def bump(c: Counter): Unit = {
    require(c.n < Int.MaxValue)
    c.last = c.n
    c.n = c.n + 1
    c.count = c.count + 1
  }

  def reset(c: Counter): Unit = c.count = 0

  def countdown(x: Int): Int = {
    @ghost var steps: BigInt = 0
    var i = x
    while (i > 0) {
      decreases(i)
      i -= 1
      steps += 1
    }
    i
  }

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState

    val c = Counter(0, 0, 0)
    bump(c)
    bump(c)
    reset(c)
    StdOut.println(c.n)          // 2
    StdOut.println(c.last)       // 1
    StdOut.println(countdown(5)) // 0
  }
}
