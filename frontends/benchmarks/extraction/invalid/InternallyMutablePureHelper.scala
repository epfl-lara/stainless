import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutablePureHelper {
  class Cache(@internallyMutable private var last: BigInt) {
    // A @pure method could expose the field to callers
    @pure
    def peek: BigInt = last
  }
}
