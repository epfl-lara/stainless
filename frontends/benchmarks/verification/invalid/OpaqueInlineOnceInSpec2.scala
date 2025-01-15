import stainless._
import stainless.lang._
import stainless.annotation._

object OpaqueInlineOnceInSpec2 {
  @opaque
  @inlineOnce
  def f(x: BigInt): BigInt = {
    require(x >= 0)
    BigInt(42)
  }.ensuring(_ >= 0)

  def ansertToLifeHowOriginal(x: BigInt, y: BigInt): Unit = {
    require(x >= 0)
    require(y == f(x))
    assert(y == 42)
  }
}
