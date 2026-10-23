import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutablePrivateHelper {
  class Cache(@internallyMutable private var last: BigInt) {
    // A private method could expose the field through a public caller
    private def peek: BigInt = last
    def leak: BigInt = peek
  }
}
