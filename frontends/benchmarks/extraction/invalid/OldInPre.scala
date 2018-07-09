import stainless.lang._

object Main {
  def f(x: Int): Int = {
    require(old(x) == x)
    x
  }
}
