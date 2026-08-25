import stainless._
import stainless.annotation._

object BigIntOverflow {
  // With --genc-bigint-as=uint32, verification injects a VC that x + x stays within
  // [0, 2^32-1]. With no upper bound on x, that VC is invalid
  // ("Addition out of uint32 range").
  @cCode.`export`
  def double(x: BigInt): BigInt = {
    require(0 <= x)
    x + x
  }
}
