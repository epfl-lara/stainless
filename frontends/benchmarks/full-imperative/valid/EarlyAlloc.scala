import stainless.lang._
import stainless.annotation._
object Allocation {
  case class Box(var value: BigInt) extends AnyHeapRef
  case class BoxBox(var value: BigInt, var box: Box) extends AnyHeapRef

  @allocates
  def earlyAlloc(bb: BoxBox, v: BigInt): Box = {
    val b = new Box(v)
    val r = bb.box
    assert(b != r)
    r
  }
}
