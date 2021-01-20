
import stainless.lang._
import stainless.annotation._

object Allocation {
  case class Box(var value: BigInt) extends AnyHeapRef
  case class BoxBox(var value: BigInt, var box: Box) extends AnyHeapRef

  @allocates
  def subAllocated(bb: BoxBox): Box = {
    reads(Set(bb))
    bb.box
  } ensuring { res =>
    allocated(res)
  }

  @extern
  @allocates
  def alloc: Box = {
    Box(0)
  } ensuring {
    res => fresh(res) && res.value == 0
  }

  @allocates
  def testFreshDoesNotAlias1(b1: Box): Unit = {
    reads(Set(b1))
    val b2 = alloc
    assert(b2.value == 0)
    b2.value += 1
  } ensuring { _ =>
    b1.value == old(b1.value)
  }

  @allocates
  def testFreshDoesNotAlias2(b1: Box): BigInt = {
    reads(Set(b1))
    modifies(Set(b1))
    val b2 = alloc
    b1.value += 1
    b2.value
  } ensuring { res =>
    res == 0
  }

  def read(b: Box): BigInt = {
    reads(Set(b))
    b.value
  }

  @allocates
  def testReadFresh: Unit = {
    val b = alloc
    // Reading b isnt' visible outside the function (since fresh), so it is allowed
    read(b)
  }

  @allocates
  def testHeapAccessInsideFresh(bb: BoxBox): Unit = {
    reads(Set(bb))
    modifies(Set(bb))
    bb.box = alloc
    assert(fresh(bb.box))
  }
}
