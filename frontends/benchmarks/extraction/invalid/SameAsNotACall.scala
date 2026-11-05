import stainless.lang._
import stainless.lang.StaticChecks._

object SameAsNotACall {
  def inc(x: BigInt): BigInt = {
    x + 1
  }.ensuring(sameAs(x + 1))
}
