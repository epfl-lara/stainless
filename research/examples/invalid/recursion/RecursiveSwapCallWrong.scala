import stainless.lang._

object RecursiveSwapCallWrong {
  case class Box(var value: BigInt)
  case class Holder(var a: Box, var b: Box)

  def swap(h: Holder): Unit = {
    val t = h.a
    h.a = h.b
    h.b = t
  }

  def swapN(h: Holder, n: BigInt): Unit = {
    require(n >= 0)
    decreases(n)
    if (n > 0) {
      swap(h)
      swapN(h, n - 1)
    }
  }

  def f(h: Holder): Unit = {
    val x = h.a
    swapN(h, 2)
    x.value = 7

    assert(h.b.value == 7)
  }
}
