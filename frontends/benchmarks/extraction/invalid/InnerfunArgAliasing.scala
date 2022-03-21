import stainless._
import stainless.lang._
import stainless.annotation._

object InnerfunArgAliasing {

  case class Box(var value: Int)

  def outer(x: Box, y: Box, cond: Boolean): Unit = {
    val z = if (cond) y else x

    def inner(innoncentLooking: Box): Unit = {
      val oldX = x.value
      innoncentLooking.value = 1234
      assert(innoncentLooking.value == 1234)
      // This must hold because we assume x and innoncentLooking are disjoint
      assert(x.value == oldX)
    }

    // Illegal aliasing due to z aliasing x for cond = false
    inner(z)
  }
}
