import stainless.math.*

// sanity check to ensure lemmas do not imply false
// since the lemmas are verified in Stainless, something has gone seriously wrong if this test fails
object FloatingPointFunctionsContradiction {
  def test(d1: Double, d2: Double,  d3: Double, d4: Double, d5: Double, d6: Double, d7: Double, d8: Double, d9: Double,
           d10: Double, d11: Double, d12: Double, d13: Double, d14: Double, d15: Double, d16: Double, d17: Double,
           d18: Double, d19: Double, d20: Double, d21: Double): Unit = {
    sin(d1)
    cos(d2)
    tan(d3)
    asin(d4)
    acos(d5)
    atan(d6)
    atan2(d7, d8)
    cbrt(d9)
    hypot(d10, d11)
    log(d12)
    log10(d13)
    exp(d14)
    expm1(d15)
    log1p(d16)
    sinh(d17)
    cosh(d18)
    tanh(d19)
    pow(d20, d21)
    ()
  }.ensuring(false)
}
