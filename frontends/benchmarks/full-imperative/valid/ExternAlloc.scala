
import stainless.lang._
import stainless.annotation._

object ExternAlloc {
  case class Box(var value: BigInt) extends AnyHeapRef

  @extern
  @allocates
  def externAlloc: Box = {
    Box(0)
  } ensuring { res =>
    fresh(res)
  }

  @allocates
  def test(b1: Box): Unit = {
    reads(Set(b1))
    val b2 = externAlloc
  } ensuring {
    b1.value == old(b1.value)
  }
}
