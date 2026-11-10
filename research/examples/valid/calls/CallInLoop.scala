import stainless.lang._

object CallInLoop {
  case class Box(var value: BigInt)

  def make(v: BigInt): Box = Box(v)

  def f(n: BigInt): Unit = {
    require(n >= 0)

    var last = Box(-1)
    var i = BigInt(0)
    (while (i < n) {
      decreases(n - i)
      val b = make(i)
      assert(last.value == i - 1)
      last = b
      i = i + 1
    }).invariant(last.value == i - 1)
  }
}
