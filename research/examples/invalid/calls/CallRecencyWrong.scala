import stainless.lang._

object CallRecencyWrong {
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
      assert(prev.value == 7)
      prev = cur
      i = i + 1
    }).invariant(i >= 1)
  }
}
