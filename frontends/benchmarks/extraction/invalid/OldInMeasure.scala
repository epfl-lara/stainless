import stainless.lang._

object Main {
  def f(x: Int): Int = {
    decreases(old(x))
    x
  }
}
