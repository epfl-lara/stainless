
import stainless.lang._
import stainless.collection.List

object BadEquality1 {
  case class Box(var value: BigInt) extends AnyHeapRef

  def wrong(l1: List[Box], l2: List[Box]): Boolean = {
    l1 == l2
  }
}
