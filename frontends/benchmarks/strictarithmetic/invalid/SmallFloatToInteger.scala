package strictarithmetic.invalid

object SmallFloatToInteger {
  def test(f: Float): Unit = {
    require(f == -9223373136366403584f)
    assert(f.toLong == -9223372036854775808f)
  }
}
