import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutableTraitVar {
  trait T {
    @internallyMutable var x: BigInt
  }
}
