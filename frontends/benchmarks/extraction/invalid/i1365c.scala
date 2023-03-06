import stainless._
import stainless.lang._
import stainless.annotation._

// Adapted from InnerfunArgAliasing3
object i1365c {

  case class Box(var value: Int)

  def outer(boxes: Array[Box], i: Int, j: Int): Unit = {
    require(0 <= i && i < boxes.length)
    require(0 <= j && j < boxes.length)

    // This must be rejected because it captures boxes.
    // even if we do not call inner
    val inner = (innoncentLooking: Box) => {
      val oldI = boxes(i).value
      innoncentLooking.value = 1234
      assert(innoncentLooking.value == 1234)
    }
  }
}
