import stainless.lang.*

object FPNaNNotPos {
  def f(a: Float): Float = {
    require(!a.isNegative) // can be NaN
    decreases(a)
    f(a / 2)
  }
}
