import stainless.lang._

object ParameterStoredIntoArray {
  case class Box(var value: BigInt)

  def insert(a: Array[(BigInt, Box)], time: BigInt, b: Box): Unit = {
    require(a.length > 0)
    swap(a, 0, Array((time, b)), 0)
  }

  def f(a: Array[(BigInt, Box)], b: Box): Unit = {
    require(a.length > 0)

    insert(a, 1, b)
    val old = a(0)._2.value

    b.value = old + 1

    assert(a(0)._2.value == old)
  }
}
