import stainless.lang._

object EarlyReturnInLoop {
  case class Box(var value: BigInt)

  def f(cond: Boolean): Unit = {
    var a = Box(4)
    var b = a
    var i = BigInt(0)

    (while (i < 3) {
      decreases(3 - i)
      if (cond && i == 1) {
        return
      }
      a.value = a.value + 1
      i = i + 1
    }).invariant(i >= 0 && i <= 3 && a.value == 4 + i && b == a)

    assert(b.value == 7)
  }
}
