import stainless.annotation._
import stainless.lang._
import stainless.io._

object Nested {

  @extern
  def main(args: Array[String]): Unit = _main()

  def _main(): Int = {
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
