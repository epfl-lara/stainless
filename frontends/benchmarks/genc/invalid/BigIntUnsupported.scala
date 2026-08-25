import stainless._
import stainless.annotation._

object BigIntUnsupported {
  // BigInt is unbounded and has no C counterpart, so GenC must reject it.
  @cCode.`export`
  def test(x: Int): Int = {
    val big: BigInt = BigInt(x) + BigInt(1)
    if (big > BigInt(0)) x else -x
  }
}
