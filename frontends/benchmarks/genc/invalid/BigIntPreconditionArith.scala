import stainless._
import stainless.annotation._

object BigIntPreconditionArith {
  // Preconditions of exported functions are compiled to runtime checks against
  // unverified C callers, so with --genc-bigint-as=uint32 no VC can bound their
  // arithmetic: `x * x` itself could overflow inside the check. GenC rejects this;
  // only comparisons on BigInt are allowed in exported preconditions.
  @cCode.`export`
  def test(x: BigInt): BigInt = {
    require(x * x <= 100)
    x + 1
  }
}
