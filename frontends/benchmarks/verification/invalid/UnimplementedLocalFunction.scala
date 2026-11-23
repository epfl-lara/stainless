import stainless.lang._

// The `???` body of a local function.
object UnimplementedLocalFunction {
  def test(x: BigInt): BigInt = {
    require(x >= 0)
    def bigger(y: BigInt): BigInt = {
      require(y >= 0)
      (??? : BigInt)
    }.ensuring(_ > y)
    bigger(x)
  }.ensuring(_ > x)
}
