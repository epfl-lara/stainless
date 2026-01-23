import stainless.lang.*

object FloatingPoints4 {
  def testBasicFloatToIntegerCasts(zero: Float, one: Float): Unit = {
    require(zero == 0f && one == 1f)
    assert((-one).toByte == -1)
    assert(zero.toByte == 0)
    assert(one.toByte == 1)
    assert((-one).toShort == -1)
    assert(zero.toShort == 0)
    assert(one.toShort == 1)
    assert((-one).toInt == -1)
    assert(zero.toInt == 0)
    assert(one.toInt == 1)
    assert((-one).toLong == -1)
    assert(zero.toLong == 0)
    assert(one.toLong == 1)
  }

  def testBasicDoubleToIntegerCasts(zero: Double, one: Double): Unit = {
    require(zero == 0d && one == 1d)
    assert((-one).toByte == -1)
    assert(zero.toByte == 0)
    assert(one.toByte == 1)
    assert((-one).toShort == -1)
    assert(zero.toShort == 0)
    assert(one.toShort == 1)
    assert((-one).toInt == -1)
    assert(zero.toInt == 0)
    assert(one.toInt == 1)
    assert((-one).toLong == -1)
    assert(zero.toLong == 0)
    assert(one.toLong == 1)
  }

  def testSmallFPToIntCasts(f1: Float, f2: Float, f3: Float, f4: Float, d1: Double, d2: Double, d3: Double, d4: Double): Unit = {
    require(f1 == -2147483520f && f2 == -2147483648f && f3 == -2147483904f && f4 == Float.NegativeInfinity)
    require(d1 == -2147483647.999d && d2 == -2147483648d && d3 == -2147483648.001d && d4 == Double.NegativeInfinity)
    assert(f1.toInt == -2147483520)
    assert(f2.toInt == -2147483648)
    assert(f3.toInt == -2147483648)
    assert(f4.toInt == -2147483648)
    assert(d1.toInt == -2147483647)
    assert(d2.toInt == -2147483648)
    assert(d3.toInt == -2147483648)
    assert(d4.toInt == -2147483648)
  }

  def testLargeFPToIntCasts(f1: Float, f2: Float, f3: Float, f4: Float, d1: Double, d2: Double, d3: Double, d4: Double): Unit = {
    require(f1 == 2147483520f && f2 == 2147483648f && f3 == 2147483904f && f4 == Float.PositiveInfinity)
    require(d1 == 2147483646.999d && d2 == 2147483647d && d3 == 2147483647.001d && d4 == Double.PositiveInfinity)
    assert(f1.toInt == 2147483520)
    assert(f2.toInt == 2147483647)
    assert(f3.toInt == 2147483647)
    assert(f4.toInt == 2147483647)
    assert(d1.toInt == 2147483646)
    assert(d2.toInt == 2147483647)
    assert(d3.toInt == 2147483647)
    assert(d4.toInt == 2147483647)
  }

  def testSmallFPToLongCasts(f1: Float, f2: Float, f3: Float, f4: Float, d1: Double, d2: Double, d3: Double, d4: Double): Unit = {
    require(f1 == -9223371487098961920f && f2 == -9223372036854775808f && f3 == -9223373136366403584f && f4 == Float.NegativeInfinity)
    require(d1 == -9223372036854774784d && d2 == -9223372036854775808d && d3 == -9223372036854777856d && d4 == Double.NegativeInfinity)
    assert(f1.toLong == -9223371487098961920f)
    assert(f2.toLong == -9223372036854775808f)
    assert(f3.toLong == -9223372036854775808f)
    assert(f4.toLong == -9223372036854775808f)
    assert(d1.toLong == -9223372036854774784d)
    assert(d2.toLong == -9223372036854775808d)
    assert(d3.toLong == -9223372036854775808d)
    assert(d4.toLong == -9223372036854775808d)
  }

  def testLargeFPToLongCasts(f1: Float, f2: Float, f3: Float, f4: Float, d1: Double, d2: Double, d3: Double, d4: Double): Unit = {
    require(f1 == 9223371487098961920f && f2 == 9223372036854775808f && f3 == 9223373136366403584f && f4 == Float.PositiveInfinity)
    require(d1 == 9223372036854774784d && d2 == 9223372036854775808d && d3 == 9223372036854777856d && d4 == Double.PositiveInfinity)
    assert(f1.toLong == 9223371487098961920f)
    assert(f2.toLong == 9223372036854775807f)
    assert(f3.toLong == 9223372036854775807f)
    assert(f4.toLong == 9223372036854775807f)
    assert(d1.toLong == 9223372036854774784d)
    assert(d2.toLong == 9223372036854775807d)
    assert(d3.toLong == 9223372036854775807d)
    assert(d4.toLong == 9223372036854775807d)
  }

  def testNaNToIntegerCasts(f: Float, d: Double): Unit = {
    require(f.isNaN && d.isNaN)
    assert(f.toByte == 0)
    assert(f.toShort == 0)
    assert(f.toInt == 0)
    assert(f.toLong == 0)
    assert(d.toByte == 0)
    assert(d.toShort == 0)
    assert(d.toInt == 0)
    assert(d.toLong == 0)
  }
}