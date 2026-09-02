import stainless.lang._
import stainless.annotation._

object UnfoldOpaqueVal {
  @opaque
  def opaqueFn(x: BigInt): BigInt = x + 1

  def test(x: BigInt): Unit = {
    val y = opaqueFn(x)
    unfolding(y)
    assert(y == x + 1)
  }
}
