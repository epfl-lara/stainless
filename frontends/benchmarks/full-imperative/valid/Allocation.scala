
import stainless.lang._
import stainless.annotation._

object Allocation {
  case class Box(var value: BigInt) extends AnyHeapRef
  case class BoxBox(var value: BigInt, var box: Box) extends AnyHeapRef

  @allocates
  def subAllocated(bb: BoxBox): Box = {
    bb.box
  } ensuring { res =>
    allocated(res)
  }

  @allocates
  def alloc: Box = {
    Box(0)
  } ensuring {
    res => fresh(res)
  }

  @allocates
  def testFreshDoesNotAlias1(b1: Box): Unit = {
    val b2 = alloc
    b2.value += 1
  } ensuring { _ =>
    b1.value == old(b1.value)
  }

  @allocates
  def testFreshDoesNotAlias2(b1: Box): BigInt = {
    val b2 = Box(0)
    b1.value += 1
    b2.value
  } ensuring { res =>
    res == 0
  }
}
