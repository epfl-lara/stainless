import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutableParam {
  def f(@internallyMutable x: BigInt): BigInt = x
}
