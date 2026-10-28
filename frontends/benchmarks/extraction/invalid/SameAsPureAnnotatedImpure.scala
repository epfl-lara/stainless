import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object SameAsPureAnnotatedImpure {
  case class Box(var v: BigInt)

  // Annotated @pure but has effects: rejected by the usual @pure check.
  @pure
  def impureNext(b: Box): BigInt = {
    b.v += 1
    b.v
  }

  def next(b: Box): BigInt = {
    b.v + 1
  }.ensuring(sameAs(impureNext(b)))
}
