import stainless.lang._

object ArrayOfPairs {
  case class A(var x: Int)
  def insert(array: Array[(Int, A)], time: Int, elem: A): Unit = {
    require(array.length > 0)
    swap(array, 0, Array((time, elem)), 0)
  }
}
