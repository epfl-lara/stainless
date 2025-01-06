
import stainless.lang._

object Aliasing {
  case class Box(var value: BigInt) extends AnyHeapRef

  def aliased(b1: Box, b2: Box): (BigInt, BigInt) = {
    require(!(b1.refEq(b2)))
    reads(Set(b1, b2))
    modifies(Set(b2))
    val b1old = b1.value
    b2.value += 1
    val b1new = b1.value
    (b1old, b1new)
 }.ensuring(res =>
    res._1 == res._2
  )
}
