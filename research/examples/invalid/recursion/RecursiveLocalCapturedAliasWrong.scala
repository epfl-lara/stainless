import stainless.lang._

object RecursiveLocalCapturedAliasWrong {
  case class Box(var value: BigInt)
  case class Holder(var box: Box)

  def set(b: Box): Unit = {
    b.value = 5
  }

  def f(h: Holder): Unit = {
    val b = h.box
    val a = h.box
    def g(k: BigInt): Unit = {
      require(k >= 0)
      decreases(k)
      if (k > 0) g(k - 1) else set(b)
    }
    b.value = 1
    g(2)
    assert(a.value == 1)
  }
}
