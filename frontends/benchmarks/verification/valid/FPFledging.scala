import stainless.math._

object FPFledging {
  def test1(x: Double): Unit = {
    assert(Double.longBitsToDouble(Double.doubleToRawLongBits(x)) == x)
  }

  def test2(x: Long): Unit = {
    Double.longBitsToDoublePost(x)
    assert(Double.doubleToRawLongBits(Double.longBitsToDouble(x)) == x)
  }

  def test3(x: Float): Unit = {
    assert(Float.intBitsToFloat(Float.floatToRawIntBits(x)) == x)
  }

  def test4(x: Int): Unit = {
    Float.intBitsToFloatPost(x)
    assert(Float.floatToRawIntBits(Float.intBitsToFloat(x)) == x)
  }
}