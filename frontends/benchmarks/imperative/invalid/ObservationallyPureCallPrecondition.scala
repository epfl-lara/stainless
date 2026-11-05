import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object ObservationallyPureCallPrecondition {
  @pure
  def pureId(x: BigInt): BigInt = x

  class Memo(@internallyMutable private var last: BigInt) {
    def get(x: BigInt): BigInt = {
      require(x >= 0)
      last = x
      x
    }.ensuring(sameAs(pureId(x)))
  }

  // The replaced call still checks the precondition of `get`
  def caller(m: Memo): BigInt = m.get(-1)
}
