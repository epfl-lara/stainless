import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutableOtherInstance {
  @pure def pureId(x: BigInt): BigInt = x

  class Cache(@internallyMutable private var last: BigInt) {
    def touch(other: Cache, x: BigInt): BigInt = {
      other.last = x
      x
    }.ensuring(sameAs(pureId(x)))
  }
}
