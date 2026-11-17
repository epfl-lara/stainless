import stainless.lang._

object CallRecency {
  case class Box(var value: BigInt)

  def make(v: BigInt): Box = Box(v)

  def f(n: BigInt): Unit = {
    require(n >= 2)

    var prev = make(0)
    var i = BigInt(1)
    (while (i < n) {
      decreases(n - i)
      val cur = make(i)
      cur.value = 7
      assert(i == 1 || prev.value == 7)
      prev = cur
      i = i + 1
    }).invariant(i >= 1 && (i == 1 || prev.value == 7))
  }
}
