import stainless.lang._
import stainless.annotation._

object ArrayShenanigans1 {
  case class Ref(var x: Int)

  def test(arr: Array[Ref], i: Int, j: Int): Unit = {
    require(0 <= i && i < arr.length)
    require(0 <= j && j < arr.length)

    val oldJ = arr(j).x
    arr(i).x = 42
    assert(arr(j).x == oldJ)
  }
}
