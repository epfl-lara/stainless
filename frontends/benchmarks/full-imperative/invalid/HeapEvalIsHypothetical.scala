import stainless.lang._
import stainless.annotation._

object HeapEvalIsHypotheticalExample {
  case class Cell(var value: BigInt) extends AnyHeapRef

  def getHypotheticalIsHypothetical(c: Cell): Unit = {
    reads(Set(c))
    modifies(Set(c))
    val heapA = Heap.get
    val heapB = heapA.eval {
      c.value += 1
      Heap.get
    }
    // Our implicit heap was unaffected, so this does not hold:
    assert(heapB.eval { c.value } == c.value)
  }
}
