import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutableWriteInPublicMethod {
  class Cache(@internallyMutable private var last: BigInt) {
    def reset(): Unit = {
      last = 0
    }
  }
}
