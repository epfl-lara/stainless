import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object ObservationallyPureOverridable {
  @pure
  def pureId(x: BigInt): BigInt = x

  sealed trait T {
    // Calls could dispatch to an override, so they cannot be replaced by `pureId`
    def get(x: BigInt): BigInt = {
      x
    }.ensuring(sameAs(pureId(x)))
  }
  case class A() extends T
}
