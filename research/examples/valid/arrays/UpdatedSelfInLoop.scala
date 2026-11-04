import stainless.lang._

object UpdatedSelfInLoop {
  case class Box(var value: BigInt)

  def f(n: Int): Unit = {
    require(0 <= n)

    var a = Array(Box(1), Box(2))
    var i = 0
    (while (i < n) {
      decreases(n - i)
      a = a.updated(0, Box(0))
      i += 1
    }).invariant(0 <= i && i <= n && a.length == 2)

    a(1).value = 3

    assert(a(1).value == 3)
  }
}
