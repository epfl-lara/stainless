import stainless.lang._

object FloatingPoints2 {
  def testStainlessMathFloatMethods() = {
    val nan = Float.NaN
    val inf = Float.PositiveInfinity
    val ninf = Float.NegativeInfinity
    val zero = 0f
    val nzero = -0f
    assert(!nan.isPositive)
    assert(!nan.isNegative)
    assert(!nan.isZero)
    assert(inf.isPositive)
    assert(!inf.isNegative)
    assert(!inf.isZero)
    assert(!ninf.isPositive)
    assert(ninf.isNegative)
    assert(!ninf.isZero)
    assert(zero.isPositive)
    assert(!zero.isNegative)
    assert(zero.isZero)
    assert(!nzero.isPositive)
    assert(nzero.isNegative)
    assert(nzero.isZero)
  }

  def testStainlessMathDoubleMethods() = {
    val nan = Double.NaN
    val inf = Double.PositiveInfinity
    val ninf = Double.NegativeInfinity
    val zero = 0d
    val nzero = -0d
    assert(!nan.isPositive)
    assert(!nan.isNegative)
    assert(!nan.isZero)
    assert(inf.isPositive)
    assert(!inf.isNegative)
    assert(!inf.isZero)
    assert(!ninf.isPositive)
    assert(ninf.isNegative)
    assert(!ninf.isZero)
    assert(zero.isPositive)
    assert(!zero.isNegative)
    assert(zero.isZero)
    assert(!nzero.isPositive)
    assert(nzero.isNegative)
    assert(nzero.isZero)
  }
}