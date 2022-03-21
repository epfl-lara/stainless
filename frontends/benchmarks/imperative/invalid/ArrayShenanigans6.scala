import stainless.lang._
import stainless.annotation._

object ArrayShenanigans6 {

  def test(arr: Array[Int], i: Int, j: Int, k: Int): Unit = {
    require(0 <= i && i < arr.length)
    require(0 <= j && j < arr.length)
    require(0 <= k && k < arr.length)

    val oldJ = arr(j)
    val oldK = arr(k)
    val arr2 = arr.updated(i, 123)
    assert(arr2(j) == oldJ || arr2(k) == oldK)
  }
}
