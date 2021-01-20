
import stainless.lang._
import stainless.annotation._

object ExternAlloc {
  case class Box(var value: BigInt) extends AnyHeapRef

  @extern
  @allocates
  def alloc: Box = {
    Box(0)
  } ensuring { res =>
    fresh(res) && res.value == 0
  }

  @allocates
  def test(b1: Box): Unit = {
    reads(Set(b1))
    val b2 = alloc
    assert(b2.value == 0) // this passes with the set encoding only
  } ensuring { res =>
    b1.value == old(b1.value)
  }

  @allocates
  def allocTwice: (Box, Box) = {
    val b1 = alloc
    val b2 = alloc
    (b1, b2)
  } ensuring { res =>
    fresh(res._1) && fresh(res._2) && res._1 != res._2
  }
}
