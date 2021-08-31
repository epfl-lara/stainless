import stainless.lang._
import stainless.annotation._

object FirstClassHeapExample {
  case class Cell(var value: BigInt) extends AnyHeapRef

  def getAndCompareHeapRegions(c1: Cell, c2: Cell): Unit = {
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

  def rewindAndEvaluate(c: Cell): BigInt = {
    reads(Set(c))
    modifies(Set(c))
    val heapA = Heap.get
    c.value += 1
    heapA.eval { c.value }
  } ensuring (_ == old(c.value))

  def getHypothetical(c: Cell): Unit = {
    reads(Set(c))
    modifies(Set(c))
    val heapA = Heap.get
    val heapB = heapA.eval {
      c.value += 1
      Heap.get
    }
    assert(heapA == Heap.get)
    assert(heapB.eval { c.value } == c.value + 1)
  }

  def compareHypotheticalHeaps(c1: Cell, c2: Cell): Unit = {
    reads(Set(c1, c2))
    modifies(Set(c1, c2))
    require(c1 != c2)
    val heapA = Heap.get
    val heapB1 = heapA.eval {
      c1.value += 1
      c2.value += 2
      Heap.get
    }
    val heapB2 = heapA.eval {
      c2.value += 2
      c1.value += 3
      Heap.get
    }
    // Even though
    // - c1 and c2 are modified in different orders, and
    // - c1 is incremented by a different value
    // we can nonetheless show that the two resulting heaps agree on c2:
    assert(Heap.unchanged(Set(c2), heapB1, heapB2))
  }
}
