import stainless.lang._

object CallsEqualIndicesWrong {
  case class Box(var value: BigInt)

  def set(x: Box, y: Box): Unit = {
    x.value = 1
    y.value = 2

    assert(x.value == 1)
  }

  def f(a: Array[Box], i: Int, k: Int): Unit = {
    require(0 <= i && i < a.length && 0 <= k && k < a.length)

    set(a(i), a(k))
  }
}
