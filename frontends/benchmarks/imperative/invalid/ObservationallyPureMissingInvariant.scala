import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object ObservationallyPureMissingInvariant {
  @pure
  def pureDouble(x: BigInt): BigInt = 2 * x

  // Without an invariant relating the cache to `pureDouble`, a cache hit may return a wrong value,
  // so the lowered postcondition `res == pureDouble(old(x))` cannot be proven.
  case class Doubler(@internallyMutable private var last: (BigInt, BigInt)) {
    def cachedDouble(x: BigInt): BigInt = {
      if (x == last._1) last._2
      else {
        val r = 2 * x
        last = (x, r)
        r
      }
    }.ensuring(sameAs(pureDouble(x)))
  }
}
