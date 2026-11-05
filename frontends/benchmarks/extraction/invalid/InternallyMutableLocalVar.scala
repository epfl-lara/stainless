import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutableLocalVar {
  def f(): BigInt = {
    @internallyMutable var y: BigInt = 0
    y += 1
    y
  }
}
