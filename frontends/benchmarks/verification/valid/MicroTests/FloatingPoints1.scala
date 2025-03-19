object FloatingPoints1 {
  def testFloatMethods() = {
    val nan = Float.NaN
    val inf = Float.PositiveInfinity
    val ninf = Float.NegativeInfinity
    val one = 1f
    assert(nan.isNaN)
    assert(!nan.isInfinity)
    assert(!nan.isInfinite)
    assert(!nan.isNegInfinity)
    assert(!nan.isPosInfinity)
    assert(!nan.isFinite)
    assert(!inf.isNaN)
    assert(inf.isInfinity)
    assert(inf.isInfinite)
    assert(!inf.isNegInfinity)
    assert(inf.isPosInfinity)
    assert(!inf.isFinite)
    assert(!ninf.isNaN)
    assert(ninf.isInfinity)
    assert(ninf.isInfinite)
    assert(ninf.isNegInfinity)
    assert(!ninf.isPosInfinity)
    assert(!ninf.isFinite)
    assert(!one.isNaN)
    assert(!one.isInfinity)
    assert(!one.isInfinite)
    assert(!one.isNegInfinity)
    assert(!one.isPosInfinity)
    assert(one.isFinite)
  }

  def testDoubleMethods() = {
    val nan = Double.NaN
    val inf = Double.PositiveInfinity
    val ninf = Double.NegativeInfinity
    val one = 1d
    assert(nan.isNaN)
    assert(!nan.isInfinity)
    assert(!nan.isInfinite)
    assert(!nan.isNegInfinity)
    assert(!nan.isPosInfinity)
    assert(!nan.isFinite)
    assert(!inf.isNaN)
    assert(inf.isInfinity)
    assert(inf.isInfinite)
    assert(!inf.isNegInfinity)
    assert(inf.isPosInfinity)
    assert(!inf.isFinite)
    assert(!ninf.isNaN)
    assert(ninf.isInfinity)
    assert(ninf.isInfinite)
    assert(ninf.isNegInfinity)
    assert(!ninf.isPosInfinity)
    assert(!ninf.isFinite)
    assert(!one.isNaN)
    assert(!one.isInfinity)
    assert(!one.isInfinite)
    assert(!one.isNegInfinity)
    assert(!one.isPosInfinity)
    assert(one.isFinite)
  }

  def testFloatIsFiniteIdentities(f: Float) = {
    assert(!f.isNaN || !f.isFinite)
    assert(!f.isInfinity || !f.isFinite)
    assert(!f.isInfinite || !f.isFinite)
    assert(!f.isPosInfinity || !f.isFinite)
    assert(!f.isNegInfinity || !f.isFinite)
  }

  def testDoubleIsFiniteIdentities(d: Double) = {
    assert(!d.isNaN || !d.isFinite)
    assert(!d.isInfinity || !d.isFinite)
    assert(!d.isInfinite || !d.isFinite)
    assert(!d.isPosInfinity || !d.isFinite)
    assert(!d.isNegInfinity || !d.isFinite)
  }

  def testImplicitCasting() = {
    val b: Byte = 1
    val s: Short = 2
    val i: Int = 3
    val l: Long = 4
    val f: Float = 5
    val fb: Float = b
    val fs: Float = s
    @annotation.nowarn("cat=deprecation") // deprecated since precision may be lost
    val fi: Float = i
    @annotation.nowarn("cat=deprecation")
    val fl: Float = l
    val db: Double = b
    val ds: Double = s
    val di: Double = i
    @annotation.nowarn("cat=deprecation")
    val dl: Double = l
    val df: Double = f
    assert(fb == b && b == fb)
    assert(fb == b && b == fb)
    assert(fi == i && i == fi)
    assert(fl == l && l == fl)
    assert(db == b && b == db)
    assert(ds == s && s == ds)
    assert(di == i && i == di)
    assert(dl == l && l == dl)
    assert(df == f && f == df)
  }

  def testExplicitCasting() = {
    val b: Byte = 1
    val s: Short = 2
    val i: Int = 3
    val l: Long = 4
    val f: Float = 5
    val fb: Float = b.toFloat
    val fs: Float = s.toFloat
    val fi: Float = i.toFloat
    val fl: Float = l.toFloat
    val db: Double = b.toDouble
    val ds: Double = s.toDouble
    val di: Double = i.toDouble
    val dl: Double = l.toDouble
    val df: Double = f.toDouble
    assert(fb == b && b == fb)
    assert(fb == b && b == fb)
    assert(fi == i && i == fi)
    assert(fl == l && l == fl)
    assert(db == b && b == db)
    assert(ds == s && s == ds)
    assert(di == i && i == di)
    assert(dl == l && l == dl)
    assert(df == f && f == df)
  }

  def testArrayZeros() = {
    val floatArray: Array[Float] = new Array(10)
    val doubleArray: Array[Double] = new Array(10)
    assert(floatArray(4) == 0.0f) // arbitrary index
    assert(doubleArray(5) == 0.0d) // arbitrary index
  }
}