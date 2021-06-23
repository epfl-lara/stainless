import stainless.lang._

object ArrayOfPairs3 {
  case class A(var x: Int)

  def insert(array: Array[(Int, A)], time: Int, elem: A): Unit = {
    require(array.length > 0)
    val elemRef = Array[(Int, A)]((time, elem))
    swap[(Int, A)](array, 0, elemRef, 0)
  }
}
