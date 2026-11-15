import stainless.lang._

object LoopZeroIterationsWrong {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)

  def f(p: Holder, q: Holder, n: BigInt): Unit = {
    var k = BigInt(0)
    while (k < n) {
      decreases(n - k)
      val m = Box(1)
      p.b = m
      q.b = m
      k = k + 1
    }
    p.b.value = 5

    assert(q.b.value == 5)
  }
}
