import stainless.lang._

object HandSwap {
  case class Box(var value: BigInt)

  def f(m: MutableMap[BigInt, Box], j: BigInt, k: BigInt): Unit = {
    require(j != k)

    val t = m(j)
    m(j) = m(k)
    m(k) = t

    t.value = 9

    assert(m(k).value == 9)
  }
}
