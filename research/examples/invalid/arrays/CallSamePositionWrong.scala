import stainless.lang._

object CallSamePositionWrong {
  case class Box(var value: BigInt)

  def set(x: Box, y: Box): Unit = {
    x.value = 1
    y.value = 2
  }

  def f(a: Array[Box], i: Int, k: Int): Unit = {
    require(0 <= i && i < a.length && k == i)

    val x = a(i)
    val y = a(k)

    set(x, y)
  }
}
