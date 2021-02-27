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

  def testReturn5: Unit = {
    assert(return5 == 5)
  }
}
