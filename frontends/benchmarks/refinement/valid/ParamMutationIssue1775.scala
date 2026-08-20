package ParamMutationIssue1775
import stainless.lang._
import stainless.annotation._

object A:
  @mutable
  case class Box(var value: BigInt)

  def updateBox(b: Box with b.value >= 0, v: BigInt with v == b.value): {res: Unit with b.value >= 0} = {
    b.value = b.value + v
  }