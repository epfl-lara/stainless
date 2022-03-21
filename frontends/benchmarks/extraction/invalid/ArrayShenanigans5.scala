import stainless.lang._
import stainless.annotation._

object ArrayShenanigans5 {
  case class Ref(var x: Int)

  def test(arr: Array[Ref], i: Int, r: Ref): Unit = {
    require(0 <= i && i < arr.length)

    // Illegal aliasing
    val arr2 = arr.updated(i, r)
  }
}
