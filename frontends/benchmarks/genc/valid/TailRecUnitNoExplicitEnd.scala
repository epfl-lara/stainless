import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecUnitWithNoExplicitEnd {
  def countDown(n: Int): Unit =
    require(n >= 0)
    decreases(n)
    if (n > 0) countDown(n - 1)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    countDown(1000000)
  }
}
