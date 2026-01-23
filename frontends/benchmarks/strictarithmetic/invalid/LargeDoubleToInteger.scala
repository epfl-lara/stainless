package strictarithmetic.invalid

object LargeDoubleToInteger {
  def test(d: Double): Unit = {
    require(d == 9223372036854775808d)
    assert(d.toLong == 9223372036854775807d)
  }
}
