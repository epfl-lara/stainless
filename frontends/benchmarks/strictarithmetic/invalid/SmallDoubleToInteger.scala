package strictarithmetic.invalid

object SmallDoubleToInteger {
  def test(d: Double): Unit = {
    require(d == -9223372036854777856d)
    assert(d.toLong == -9223372036854775808d)
  }
}
