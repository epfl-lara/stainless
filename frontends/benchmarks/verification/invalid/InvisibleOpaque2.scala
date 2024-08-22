import stainless._
import stainless.lang._
import stainless.annotation._

object InvisibleOpaque2 {
  @opaque
  def f(x: BigInt): BigInt = {
    require(x >= 0)
    BigInt(42)
 }.ensuring(_ >= 0)

  def ansertToLifeHowOriginal(x: BigInt): Unit = {
    require(x >= 0)
    assert(f(x) == BigInt(42))
  }
}
