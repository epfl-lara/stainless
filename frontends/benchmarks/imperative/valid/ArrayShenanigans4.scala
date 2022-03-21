import stainless.lang._
import stainless.annotation._

object ArrayShenanigans4 {

  def test(arr: Array[Int], i: Int, j: Int, k: Int): Unit = {
    require(0 <= i && i < arr.length)
    require(0 <= j && j < arr.length)
    require(0 <= k && k < arr.length)

    val oldI = arr(i)
    val oldJ = arr(j)
    val oldK = arr(k)
    val arr2 = arr.updated(i, 123)
    assert(arr2(i) == 123)
    assert((j != i) ==> (arr2(j) == oldJ))
    assert((k != i) ==> (arr2(k) == oldK))
    assert(arr(i) == oldI)
    assert(arr(j) == oldJ)
    assert(arr(k) == oldK)

    arr2(j) = 456
    assert(arr(i) == oldI)
    assert(arr(j) == oldJ)
    assert(arr(k) == oldK)
  }
}
