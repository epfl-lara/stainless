import stainless.annotation._
import stainless.lang._
import stainless.io._

object TailRecNested {
  def outer(n: Int): Int = 
    require(n >= 0)
    def inner(x: Int): Int = 
      require(x >= 0)
      decreases(x)
      if x == 0 then 0
      else inner(x - 1)
    inner(n)

  @cCode.`export`
  def main(): Unit = {
    implicit val state = stainless.io.newState
    StdOut.println(outer(5)) // Expected: 0
  }
}
