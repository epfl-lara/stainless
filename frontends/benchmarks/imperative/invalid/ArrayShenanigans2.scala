import stainless.lang._
import stainless.annotation._

object ArrayShenanigans2 {
  case class Ref(var x: Int)

  def test(arr: Array[Ref], i: Int, j: Int): Unit = {
    require(0 <= i && i < arr.length)
    require(0 <= j && j < arr.length)

    val oldJ = arr(j).x
    val arri = arr(i)
    arri.x = 42
    assert(arr(j).x == oldJ)
  }
}
