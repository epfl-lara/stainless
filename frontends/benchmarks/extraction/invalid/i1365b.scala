import stainless._
import stainless.lang._
import stainless.annotation._

// Adapted from InnerfunArgAliasing1
object i1365b {

  case class Box(var value: Int)

  def outer(x: Box, y: Box, cond: Boolean): Unit = {
    val z = if (cond) y else x

    // This must be rejected because it captures x.
    // even if we do not call inner
    val inner = (innoncentLooking: Box) => {
      val oldX = x.value
      innoncentLooking.value = 1234
      assert(innoncentLooking.value == 1234)
    }
  }
}
