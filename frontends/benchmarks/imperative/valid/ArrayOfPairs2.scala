import stainless.lang._

object ArrayOfPairs2 {
  case class A(var x: Int)

  def insert(array: Array[(Int, A)], time: Int, elem: A): Unit = {
    require(array.length > 0)
    insert2(array, Array((time, elem)))
  }

  def insert2(array: Array[(Int, A)], elemRef: Array[(Int, A)]): Unit = {
    require(array.length > 0 && elemRef.length > 0)
    swap(array, 0, elemRef, 0)
  }
}
