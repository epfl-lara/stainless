import stainless._
import stainless.lang._
import stainless.annotation._

object OpaqueInlineOnce {
  @opaque
  @inlineOnce
  def f(x: BigInt): BigInt = {
    require(x >= 0)
    BigInt(42)
  }.ensuring(_ >= 0)

  def g(x: BigInt): Unit = {
    require(x >= 0)
    val y = f(x)
    assert(y == 42) // No, we only inline the specs, not the body
  }
}
