import stainless.lang._
import stainless.annotation._

object ArrayShenanigans4 {
  case class Ref(var x: Int)

  def test(arr: Array[Ref], i: Int, j: Int): Unit = {
    require(0 <= i && i < arr.length)
    require(0 <= j && j < arr.length)

    // Illegal aliasing
    val arr2 = arr.updated(i, arr(j))
  }
}
