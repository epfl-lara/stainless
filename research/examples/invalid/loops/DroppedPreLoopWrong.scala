import stainless.lang._

object DroppedPreLoopWrong {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)

  def reset(h: Holder, n: BigInt): Unit = {
    var k = BigInt(0)
    while (k < n) {
      decreases(n - k)
      h.b = Box(0)
      k = k + 1
    }
  }

  def f(h: Holder, n: BigInt): Unit = {
    val old = h.b.value
    val y = h.b
    reset(h, n)
    y.value = old + 1

    assert(n > 0 || h.b.value == old)
  }
}
