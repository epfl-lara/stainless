import stainless.lang._
import stainless.annotation._

object ArrayShenanigans1 {
  case class Ref(var x: Int)

  def test(arr: Array[Ref], i: Int, j: Int, cond: Boolean): Unit = {
    require(0 <= i && i < arr.length)
    require(0 <= j && j < arr.length)

    val arrij = if (cond) arr(i) else arr(j)
    // Illegal aliasing
    arr(i) = arrij
  }
}
