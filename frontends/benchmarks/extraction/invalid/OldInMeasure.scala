import stainless.lang._

object OldInMeasure {
  def f(x: Int): Int = {
    decreases(old(x))
    x
  }
}
