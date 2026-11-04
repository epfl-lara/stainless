import stainless.lang._

object AllocationCarriedWrong {
  case class Box(var value: BigInt)

  def f(n: BigInt): Unit = {
    var last = Box(-1)
    var i = BigInt(0)
    (while (i < n) {
      decreases(n - i)
      val a = Box(0)

      a.value = i

      assert(last.value == i)
      last = a
      i = i + 1
    }).invariant(last.value == i - 1)
  }
}
