import stainless.lang._

object AllocationCarried {
  case class Box(var value: BigInt)

  def f(n: BigInt): Unit = {
    var last = Box(-1)
    var i = BigInt(0)
    (while (i < n) {
      decreases(n - i)
      val a = Box(0)

      a.value = i

      assert(last.value == i - 1)
      last = a
      assert(last.value == i)
      i = i + 1
    }).invariant(last.value == i - 1)
  }
}
