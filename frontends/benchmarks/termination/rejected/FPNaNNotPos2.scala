import stainless.lang.*

object FPNaNNotPos2 {
  def f(a: Float): Float = {
    require(a.isNaN)
    decreases(a)
    f(a - 1)
  }
}
