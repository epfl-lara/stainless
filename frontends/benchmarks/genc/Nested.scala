import stainless.annotation._
import stainless.lang._
import stainless.io._

object Nested {

  @export
  def main(): Int = {
    f(100)
  }

  def f(x: Int): Int = {
    def gg(y: Int): Int = {
      x + y
    }
    val res = gg(15)
    StdOut.println(res)
    res
  }

}
