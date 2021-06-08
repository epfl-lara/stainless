import stainless.lang._

object ArrayOfPairs2 {
  case class A(var x: Int)

  def insert(queue: Array[(Int, A)], time: Int, elem: A): Unit = {
    require(queue.length > 0)

    val elemRef = Array((time, elem))
    swap(queue, 0, elemRef, 0)
  }
}
