import stainless.lang._

// The `???` body of a function, and of a method of a concrete class.
object UnimplementedFunction {
  def root(x: BigInt): BigInt = {
    require(x >= 0)
    (??? : BigInt)
  }.ensuring(res => res >= 0 && res * res <= x)

  case class Wrapper(x: BigInt) {
    def half: BigInt = {
      (??? : BigInt)
    }.ensuring(res => 2 * res <= x)
  }

  def test: BigInt = {
    root(16) + Wrapper(4).half
  }
}
