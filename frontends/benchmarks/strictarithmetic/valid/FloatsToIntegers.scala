import stainless.lang.*

object FloatsToIntegers {
  def testValidSmallFPToIntCasts(f1: Float, f2: Float, f3: Float, f4: Float, d1: Double, d2: Double, d3: Double, d4: Double): Unit = {
    require(!f1.isNaN && !f2.isNaN && !f3.isNaN && !f4.isNaN && !d1.isNaN && !d2.isNaN && !d3.isNaN && !d4.isNaN)
    require(f1 == -2147483520f && f2 == -2147483648f && f3 == -2147483904f && f4 == Float.NegativeInfinity)
    require(d1 == -2147483647.999d && d2 == -2147483648d && d3 == -2147483648.001d && d4 == Double.NegativeInfinity)
    assert(f1.toInt == -2147483520)
    assert(f2.toInt == -2147483648)
//    assert(f3.toInt == -2147483648)
//    assert(f4.toInt == -2147483648)
    assert(d1.toInt == -2147483647)
    assert(d2.toInt == -2147483648)
    assert(d3.toInt == -2147483648)
//    assert(d4.toInt == -2147483648)
  }

  def testValidLargeFPToIntCasts(f1: Float, f2: Float, f3: Float, f4: Float, d1: Double, d2: Double, d3: Double, d4: Double): Unit = {
    require(!f1.isNaN && !f2.isNaN && !f3.isNaN && !f4.isNaN && !d1.isNaN && !d2.isNaN && !d3.isNaN && !d4.isNaN)
    require(f1 == 2147483520f && f2 == 2147483648f && f3 == 2147483904f && f4 == Float.PositiveInfinity)
    require(d1 == 2147483646.999d && d2 == 2147483647d && d3 == 2147483647.001d && d4 == Double.PositiveInfinity)
    assert(f1.toInt == 2147483520)
//    assert(f2.toInt == 2147483647)
//    assert(f3.toInt == 2147483647)
//    assert(f4.toInt == 2147483647)
    assert(d1.toInt == 2147483646)
    assert(d2.toInt == 2147483647)
    assert(d3.toInt == 2147483647)
//    assert(d4.toInt == 2147483647)
  }

  def testValidSmallFPToLongCasts(f1: Float, f2: Float, f3: Float, f4: Float, d1: Double, d2: Double, d3: Double, d4: Double): Unit = {
    require(!f1.isNaN && !f2.isNaN && !f3.isNaN && !f4.isNaN && !d1.isNaN && !d2.isNaN && !d3.isNaN && !d4.isNaN)
    require(f1 == -9223371487098961920f && f2 == -9223372036854775808f && f3 == -9223373136366403584f && f4 == Float.NegativeInfinity)
    require(d1 == -9223372036854774784d && d2 == -9223372036854775808d && d3 == -9223372036854777856d && d4 == Double.NegativeInfinity)
    assert(f1.toLong == -9223371487098961920f)
    assert(f2.toLong == -9223372036854775808f)
//    assert(f3.toLong == -9223372036854775808f)
//    assert(f4.toLong == -9223372036854775808f)
    assert(d1.toLong == -9223372036854774784d)
    assert(d2.toLong == -9223372036854775808d)
//    assert(d3.toLong == -9223372036854775808d)
//    assert(d4.toLong == -9223372036854775808d)
  }

  def testValidLargeFPToLongCasts(f1: Float, f2: Float, f3: Float, f4: Float, d1: Double, d2: Double, d3: Double, d4: Double): Unit = {
    require(!f1.isNaN && !f2.isNaN && !f3.isNaN && !f4.isNaN && !d1.isNaN && !d2.isNaN && !d3.isNaN && !d4.isNaN)
    require(f1 == 9223371487098961920f && f2 == 9223372036854775808f && f3 == 9223373136366403584f && f4 == Float.PositiveInfinity)
    require(d1 == 9223372036854774784d && d2 == 9223372036854775808d && d3 == 9223372036854777856d && d4 == Double.PositiveInfinity)
    assert(f1.toLong == 9223371487098961920f)
//    assert(f2.toLong == 9223372036854775807f)
//    assert(f3.toLong == 9223372036854775807f)
//    assert(f4.toLong == 9223372036854775807f)
    assert(d1.toLong == 9223372036854774784d)
//    assert(d2.toLong == 9223372036854775807d)
//    assert(d3.toLong == 9223372036854775807d)
//    assert(d4.toLong == 9223372036854775807d)
  }
}
