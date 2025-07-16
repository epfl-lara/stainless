import stainless.lang.*

object FloatNaNToInteger {
  def test(f: Float): Unit = {
    require(f.isNaN)
    assert(f.toLong == 0f)
  }
}
