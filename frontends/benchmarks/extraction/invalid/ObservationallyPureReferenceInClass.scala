import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object ObservationallyPureReferenceInClass {
  class Memo(@internallyMutable private var last: BigInt) {
    @pure
    def pureId(x: BigInt): BigInt = x

    // The reference function must be defined outside of the class
    def get(x: BigInt): BigInt = {
      last = x
      x
    }.ensuring(sameAs(pureId(x)))
  }
}
