
import stainless.lang._
import stainless.annotation._

object ExternMut {

  case class Box(var value: BigInt)

  @extern
  def mutateStuff(box: Box, n: BigInt): Unit = {
    box.value = box.value * n
  }

  @extern @pure
  def dontMutateStuff(box: Box, n: BigInt): Unit = ()

  def isSameImpure = {
    val box = Box(123)
    mutateStuff(box, 2)
    box.value == 123
  }.holds // invalid

  def isSamePure = {
    val box = Box(123)
    dontMutateStuff(box, 2)
    box.value == 123
  }.holds // valid

}
