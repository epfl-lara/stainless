import stainless.lang._
import stainless.annotation._

object ArrayShenanigans2 {
  case class Ref(var x: Int)

  def test(arr: Array[Ref], i: Int, j: Int, cond: Boolean): Unit = {
    require(0 <= i && i < arr.length)
    require(0 <= j && j < arr.length)

    val arrj = if (cond) Ref(123) else arr(j)
    // Illegal aliasing
    arr(i) = arrj
  }
}
