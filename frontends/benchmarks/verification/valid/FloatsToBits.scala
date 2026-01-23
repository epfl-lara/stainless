import stainless.lang.*

object FloatsToBits {
  def testDouble(d: Double): Unit = {
    assert(java.lang.Double.doubleToLongBits(d) == java.lang.Double.doubleToLongBits(d))
    assert(d.equiv(java.lang.Double.longBitsToDouble(java.lang.Double.doubleToLongBits(d))))
  }

  def testFloat(f: Float): Unit = {
    assert(java.lang.Float.floatToIntBits(f) == java.lang.Float.floatToIntBits(f))
    assert(f.equiv(java.lang.Float.intBitsToFloat(java.lang.Float.floatToIntBits(f))))
  }
}