import stainless.lang._

object CallDistinctKeys {
  case class Box(var value: BigInt)

  def set(x: Box, y: Box): Unit = {
    x.value = 1
    y.value = 2
  }

  def f(m: MutableMap[BigInt, Box], j: BigInt, k: BigInt): Unit = {
    require(j != k)

    val x = m(j)
    val y = m(k)

    set(x, y)

    assert(m(j).value == 1)
    assert(m(k).value == 2)
  }
}
