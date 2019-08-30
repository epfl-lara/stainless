import stainless.lang._

object OldInPre {
  def f(x: Int): Int = {
    require(old(x) == x)
    x
  }
}
