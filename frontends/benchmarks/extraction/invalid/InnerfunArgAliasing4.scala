import stainless._
import stainless.lang._
import stainless.annotation._

object InnerfunArgAliasing4 {

  case class Box(var value: Int)

  def outer(boxes: Array[Box], i: Int, j: Int, z: Int): Unit = {
    require(0 <= i && i < boxes.length)
    require(0 <= j && j < boxes.length)
    require(0 <= z && z < boxes.length)

    val boxi = boxes(i)

    def inner(innoncentLooking: Box): Unit = {
      val oldI = boxi.value
      innoncentLooking.value = 1234
      assert(innoncentLooking.value == 1234)
      // This must hold because we assume boxi and innoncentLooking are disjoint
      assert(boxi.value == oldI)
    }

    // Illegal aliasing due to boxi aliasing boxes(z) for i == z and j != z
    inner(boxes.updated(j, Box(123)).apply(z))
  }
}
