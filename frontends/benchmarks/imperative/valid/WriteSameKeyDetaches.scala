import stainless.lang._

object WriteSameKeyDetaches {
  case class Box(var value: BigInt)

  def f(m: MutableMap[BigInt, Box], k: BigInt): Unit = {
    val y = m(k)

    m(k) = Box(3)
    y.value = 1

    assert(m(k).value == 3)
  }
}
