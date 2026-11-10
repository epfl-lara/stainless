import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutableCompanion {
  class Cache(@internallyMutable private var last: BigInt)
  object Cache {
    def peek(c: Cache): BigInt = c.last
  }
}
