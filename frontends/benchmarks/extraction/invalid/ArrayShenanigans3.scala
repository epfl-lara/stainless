import stainless.lang._
import stainless.annotation._

object ArrayShenanigans3 {
  case class Ref(var x: Int)

  def test(arr: Array[Ref], i: Int, j: Int, k: Int, cond: Boolean): Unit = {
    require(0 <= i && i < arr.length)
    require(0 <= j && j < arr.length)
    require(0 <= k && k < arr.length)

    val arrjk = if (cond) arr(j) else arr(k)
    // Illegal aliasing
    val arr2 = arr.updated(i, arrjk)
  }
}
