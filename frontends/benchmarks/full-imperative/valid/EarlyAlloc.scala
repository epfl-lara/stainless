import stainless.lang._
import stainless.annotation._
object Allocation {
  case class Box(var value: BigInt) extends AnyHeapRef
  case class BoxBox(var box: Box) extends AnyHeapRef

  @allocates
  def allocPrefetching(bb: BoxBox): Unit = {
    reads(Set(bb))
    // Allocation prefetching: removing this precondition makes it fail to verify 
    assert(allocated(bb.box))
    val newBox = Box(0)
    val oldBox = bb.box
    assert(newBox != oldBox)
  }
}
