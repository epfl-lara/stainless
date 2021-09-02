import stainless.lang._
import stainless.annotation._

object HeapGetProjectsReadsExample {
  case class Cell(var value: BigInt) extends AnyHeapRef

  def onlyOne(c1: Cell, c2: Cell): BigInt = {
    reads(Set(c1))
    Heap.get.eval { c2.value }
  }

  def testOne(c1: Cell, c2: Cell): Unit = {
    require(c1 != c2)
    reads(Set(c1, c2))
    modifies(Set(c2))
    c2.value = 1
    val h1 = Heap.get
    val v1 = onlyOne(c1, c2)
    assert(v1 == 1)
    c2.value = 2
    val h2 = Heap.get
    assert(Heap.unchanged(Set(c1), h1, h2))
    val v2 = onlyOne(c1, c2)
    assert(v2 == 2)
    assert(v1 == v2)
    assert(false, "Contradiction")
  }
}
