import stainless.lang._

object LoopMutation {
  case class Box(var value: BigInt)

  def f(n: BigInt): Unit = {
    require(n >= 0)

    var a = Box(0)
    var b = a
    var i = BigInt(0)

    (while (i < n) {
      decreases(n - i)
      a.value = a.value + 1
      i = i + 1
    }).invariant(a.value == i && i <= n && b == a)

    assert(a.value == n)
    assert(b.value == n)
  }
}
