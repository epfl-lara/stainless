import stainless.math.*

// since some properties of transcendental functions are axiomatized, we check that false is not implied
object FloatingPointFunctionsContradiction {
  def test(d1: Double, d2: Double,  d3: Double, d4: Double, d5: Double, d6: Double, d7: Double, d8: Double, d9: Double, d10: Double, d11: Double): Unit = {
    sin(d1)
    asin(d2)
    cos(d3)
    acos(d4)
    tan(d5)
    atan(d6)
    pow(d7, d8)
    exp(d9)
    atan2(d10, d11)
    ()
  }.ensuring(false)
}
