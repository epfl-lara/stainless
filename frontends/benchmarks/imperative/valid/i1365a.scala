import stainless._
import stainless.lang._
import stainless.annotation._

object i1365a {

  case class Box(var value: Int)

  def outer(x: Box, y: Box, cond: Boolean): Unit = {
    val z = if (cond) y else x

    val inner = (box: Box) => {
      val boxalias = box // Ok, can have alias of params
      box.value = 1234
      assert(box.value == 1234)
      assert(boxalias.value == 1234)
    }
  }
}
