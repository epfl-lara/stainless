import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutableMethod {
  @internallyMutable def f(x: BigInt): BigInt = x
}
