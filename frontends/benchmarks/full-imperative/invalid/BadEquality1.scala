
import stainless.lang._

object BadEquality1 {
  case class Box(var value: BigInt) extends AnyHeapRef

  def wrong(b1: Box, b2: Box): Boolean = {
    b1 == b2
  }
}
