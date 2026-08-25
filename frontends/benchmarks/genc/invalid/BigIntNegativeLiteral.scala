import stainless._
import stainless.annotation._

object BigIntNegativeLiteral {
  // uint32_t cannot represent negative values, so with --genc-bigint-as=uint32
  // GenC rejects BigInt literals outside [0, 2^32-1] at compile time.
  @cCode.`export`
  def test(): BigInt = {
    BigInt(-5)
  }
}
