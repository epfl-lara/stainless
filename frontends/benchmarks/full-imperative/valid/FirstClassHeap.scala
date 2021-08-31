import stainless.lang._
import stainless.annotation._

object FirstClassHeapExample {
  case class Cell(var value: BigInt) extends AnyHeapRef

  def f(c1: Cell, c2: Cell): Unit = {
    reads(Set(c1, c2))
    modifies(Set(c1, c2))
    require(c1 != c2)
    val heapA = Heap.get
    c1.value += 2
    val heapB = Heap.get
    c2.value += 3
    val heapC = Heap.get
    assert(Heap.unchanged(Set(c2), heapA, heapB))
    assert(Heap.unchanged(Set(c1), heapB, heapC))
  }
}
