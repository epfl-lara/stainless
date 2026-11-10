import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutableReadInPublicMethod {
  class Cache(@internallyMutable private var last: BigInt) {
    def peek: BigInt = last
  }
}
