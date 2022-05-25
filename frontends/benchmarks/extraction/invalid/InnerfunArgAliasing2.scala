import stainless._
import stainless.lang._
import stainless.annotation._

object InnerfunArgAliasing2 {

  case class Box(var value: Int)
  case class BBox(var box: Box)

  def outer(x: BBox, y: BBox, cond: Boolean): Unit = {
    val z = if (cond) y else x

    def inner(innoncentLooking: Box): Unit = {
      val oldX = x.box.value
      innoncentLooking.value = 1234
      assert(innoncentLooking.value == 1234)
      // This must hold because we assume x.box and innoncentLooking are disjoint
      assert(x.box.value == oldX)
    }

    // Illegal aliasing due to z.box aliasing x.box for cond = false
    inner(z.box)
  }
}
