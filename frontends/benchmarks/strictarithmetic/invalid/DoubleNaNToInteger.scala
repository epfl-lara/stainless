import stainless.lang.*

object DoubleNaNToInteger {
  def test(d: Double): Unit = {
    require(d.isNaN)
    assert(d.toLong == 0d)
  }
}
