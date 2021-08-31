import stainless.lang._
import stainless.annotation._

object HeapUnchangedInvalidExample {
  case class Cell(var value: BigInt) extends AnyHeapRef

  def f(c: Cell): Unit = {
    reads(Set(c))
    modifies(Set(c))
    val heapA = Heap.get
    c.value += 2
    val heapB = Heap.get
    assert(Heap.unchanged(Set(c), heapA, heapB))
  }
}
