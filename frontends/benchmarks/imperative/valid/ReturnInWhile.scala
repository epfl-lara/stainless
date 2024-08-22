import stainless.annotation._
import stainless.lang._
import stainless.io._

object ReturnInWhile {
  def return5: Int = {
    while (true) {
      decreases(0)
      return 5
    }
    assert(false)
    0
  }

  def returnN(n: Int): Int = {
    require(n >= 0)
    var i = 0
    (while (true) {
      decreases(n - i)
      if (i == n) return i
      i += 1
    }).invariant(0 <= i && i <= n)

    assert(false, "unreachable code")
    0
 }.ensuring((res: Int) => res == n)

  def tests: Unit = {
    assert(return5 == 5)
    assert(returnN(100) == 100)
  }
}
