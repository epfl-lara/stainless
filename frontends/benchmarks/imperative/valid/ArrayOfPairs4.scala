import stainless.lang._

object ArrayOfPairs4 {
  case class A(var x: Int)

  def insert(array: Array[(Int, A)], time: Int, elem: A): Unit = {
    require(array.length > 0)
    insert2(array, Array((time, elem)), 0, 0)
  }

  def insert2(array: Array[(Int, A)], elemRef: Array[(Int, A)], i: Int, j: Int): Unit = {
    require(0 <= i && i < array.length)
    require(0 <= j && j < elemRef.length)
    swap(array, i, elemRef, j)
  }
}
