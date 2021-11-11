import stainless.annotation._
import stainless.lang._
import stainless.io._

object Nested {

  @cCode.`export`
  def main(): Int = {
    f(100)
  }

  def f(x: Int): Int = {
    require(0 <= x && x <= 100)

    def gg(y: Int): Int = {
      require(0 <= y && y <= 100)
      x + y
    }

    val res = gg(15)
    StdOut.println(res)(newState)
    res
  }

}
