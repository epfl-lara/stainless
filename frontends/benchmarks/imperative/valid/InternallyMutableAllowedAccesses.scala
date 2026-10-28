import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutableAllowedAccesses {
  @pure
  def pureDouble(x: BigInt): BigInt = 2 * x

  class Doubler(@internallyMutable private var last: (BigInt, BigInt)) {
    // The class invariant may read internally mutable fields
    require(last._2 == pureDouble(last._1))

    // Ghost helpers may read them
    @ghost
    def cacheValid: Boolean = last._2 == pureDouble(last._1)

    // Observationally pure methods may read and write them
    def double(x: BigInt): BigInt = {
      if (x == last._1) last._2
      else {
        val r = 2 * x
        last = (x, r)
        r
      }
    }.ensuring(res => sameAs(pureDouble(x))(res) && cacheValid)
  }
}
