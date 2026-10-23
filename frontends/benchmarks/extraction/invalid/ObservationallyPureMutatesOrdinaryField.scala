import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object ObservationallyPureMutatesOrdinaryField {
  @pure
  def pureId(x: BigInt): BigInt = x

  class Counter(var calls: BigInt, @internallyMutable private var last: BigInt) {
    def get(x: BigInt): BigInt = {
      calls += 1
      last = x
      x
    }.ensuring(sameAs(pureId(x)))
  }
}
