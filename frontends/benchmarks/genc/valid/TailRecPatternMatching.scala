import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecPatternMatching {
  def patternMatch(x: Option[Int], acc: Int): Int = 
    require(x match {
      case None() => true
      case Some(n) => n >= 1
    })
    val measure = x match {
      case None() => 0
      case Some(n) => n
    }
    decreases(measure)
    x match
      case None() => acc
      case Some(n) if n == 1 => patternMatch(None(), acc + 1)
      case Some(n) => patternMatch(Some(n - 1), acc + 1)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(patternMatch(Some(5), 0)) // Expected: 5
  }
}
