import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object ObservationallyPureMutatesArgument {
  case class Box(var v: BigInt)

  @pure
  def pureId(x: BigInt): BigInt = x

  def get(b: Box, x: BigInt): BigInt = {
    b.v += 1
    x
  }.ensuring(sameAs(pureId(x)))
}
