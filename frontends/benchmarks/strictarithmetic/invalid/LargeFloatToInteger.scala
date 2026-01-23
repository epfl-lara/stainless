package strictarithmetic.invalid

object LargeFloatToInteger {
  def test(f: Float): Unit = {
    require(f == 9223372036854775808f)
    assert(f.toLong == 9223371487098961920f)
  }
}
