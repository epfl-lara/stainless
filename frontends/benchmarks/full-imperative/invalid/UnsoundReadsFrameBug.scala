import stainless.lang._
import stainless.annotation._

object UnsoundReadsFrameBugExample {
  case class Cell(var value: BigInt) extends AnyHeapRef

  def onlyOne(c1: Cell, c2: Cell): BigInt = {
    reads(Set(c1))
    modifies(Set(c1)) // Issue was triggered by adding modifies clause (fun. sig. changed)
    Heap.get.eval { c2.value }
  }

  def testOne(c1: Cell, c2: Cell): Unit = {
    require(c1 != c2)
    reads(Set(c1, c2))
    modifies(Set(c1, c2))
    c2.value = 1
    // NOTE: This used to erroneously pass, because the reads-frame-condition we
    //   assumed in the shim of onlyOne was incorrect.
    val v1 = onlyOne(c1, c2)
    assert(v1 == 1)
  }
}
