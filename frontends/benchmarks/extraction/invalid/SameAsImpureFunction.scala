import stainless.lang._
import stainless.lang.StaticChecks._

object SameAsImpureFunction {
  case class Box(var v: BigInt)

  def impureNext(b: Box): BigInt = {
    b.v += 1
    b.v
  }

  def next(b: Box): BigInt = {
    b.v + 1
  }.ensuring(sameAs(impureNext(b)))
}
