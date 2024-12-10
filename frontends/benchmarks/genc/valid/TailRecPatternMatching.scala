import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecPatternMatching {
  def patternMatch(x: Option[Int], acc: Int): Int = x match
    case None() => acc
    case Some(0) => patternMatch(None(), acc + 1)
    case Some(n) => patternMatch(Some(n - 1), acc + 1)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(patternMatch(Some(5), 0)) // Expected: 6
  }
}
