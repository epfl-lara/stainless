import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecComplexArgs {
  def complexArgs(n: Int): Int =
    if n <= 0 then 1
    else complexArgs(n - 1 * 2 + 1) // Complex argument

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(complexArgs(5)) // Expected: 1
  }
}
