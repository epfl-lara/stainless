package ParamMutationIssue1775
import stainless.lang._
import stainless.annotation._

object A:
  @mutable
  case class Box(var value: BigInt)

  def updateBox(b: Box with b.value >= 0, v: BigInt with v == b.value): {res: Unit with b.value >= 0} = {
    b.value = b.value + v
  }

  def updateBox2(b: Box with b.value >= 0): {res: Unit with b.value >= 0} = {
    val v: BigInt with v == b.value = b.value
    val x: BigInt with x == b.value = b.value
    b.value = b.value + v
    assert(v == x)
  }

  def updateBox3(b: Box with b.value >= 0): {res: Unit with b.value >= 0} = {
    // Let say the the b parameter gets the index b$0
    b.value = b.value + 1 // now we have b$1.value == b$0.value + 1
    val v: BigInt with v == b.value = b.value // == b$1.value == b$0.value + 1
    val x: BigInt with x == b.value = b.value // == b$1.value == b$0.value + 1
    b.value = b.value + v // now we have b$2.value == b$1.value + v, with v == b$1.value == b$0.value + 1
    assert(v == x) // should hold, as both are equal to b$1.value
  }

  def updateBox4(): {res: Box with res.value >= 0} = {
    val b: Box with b.value >= 0 = Box(0)
    val v: BigInt with v == b.value = b.value
    b.value = b.value + v
    assert(v == 0)
    b
  }