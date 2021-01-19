
import stainless.lang._
import stainless.annotation._

object ExternAlloc {
  case class Box(var value: BigInt) extends AnyHeapRef

  @extern
  @allocates
  def alloc: Box = {
    Box(0)
  } ensuring { res =>
    fresh(res)
  }

  @allocates
  def test(b1: Box): Unit = {
    reads(Set(b1))
    val b2 = alloc
    // This passes with the counter encoding:
    // val v = b2.value
    // assert(v == 41)
    // assert(v == 42)
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
