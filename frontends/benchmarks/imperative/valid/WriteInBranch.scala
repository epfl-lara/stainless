import stainless.lang._

object WriteInBranch {
  case class Box(var value: BigInt)

  def f(m: MutableMap[BigInt, Box], k: BigInt, c: Boolean): Unit = {
    val y = m(k)

    if (c) m(k) = Box(1)
    y.value = 2

    assert(c || m(k).value == 2)
    assert(!c || m(k).value == 1)
  }
}
