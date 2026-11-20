import stainless.lang._

object CallSameKeyPossibleWrong {
  case class Box(var value: BigInt)

  def set(x: Box, y: Box): Unit = {
    x.value = 1
    y.value = 2
  }

  def f(m: MutableMap[BigInt, Box], j: BigInt, k: BigInt): Unit = {
    val x = m(j)
    val y = m(k)

    set(x, y)
  }
}
