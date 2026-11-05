import stainless.lang._
import stainless.lang.StaticChecks._

object SameAsUnderDisjunction {
  def pureId(x: BigInt): BigInt = x

  def id(x: BigInt): BigInt = {
    x
  }.ensuring(res => sameAs(pureId(x))(res) || res == 0)
}
