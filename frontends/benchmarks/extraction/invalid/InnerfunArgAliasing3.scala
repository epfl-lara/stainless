import stainless._
import stainless.lang._
import stainless.annotation._

object InnerfunArgAliasing3 {

  case class Box(var value: Int)

  def outer(boxes: Array[Box], i: Int, j: Int): Unit = {
    require(0 <= i && i < boxes.length)
    require(0 <= j && j < boxes.length)

    val boxi = boxes(i)

    def inner(innoncentLooking: Box): Unit = {
      val oldI = boxi.value
      innoncentLooking.value = 1234
      assert(innoncentLooking.value == 1234)
      // This must hold because we assume boxi and innoncentLooking are disjoint
      assert(boxi.value == oldI)
    }

    // Illegal aliasing due to boxi aliasing boxes(j) for i == j
    inner(boxes(j))
  }
}
