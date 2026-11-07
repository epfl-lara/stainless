import stainless.lang.*

object FPPosNonDecreasing {
  def f(a: Float): BigInt = {
    require(a.isPositive) // can be +oo
    decreases(a)
    if a < 1.0 then 0
    else 1 + f(a / 2)
  }
}
