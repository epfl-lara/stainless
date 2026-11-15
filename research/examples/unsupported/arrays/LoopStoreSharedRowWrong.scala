import stainless.lang._

object LoopStoreSharedRowWrong {
  def f(a: Array[Array[BigInt]]): Unit = {
    require(a.length >= 2)
    val r = Array[BigInt](0)

    var i = 0
    (while (i < a.length) {
      decreases(a.length - i)
      a(i) = r
      i += 1
    }).invariant(0 <= i && i <= a.length)

    a(0)(0) = 7
    assert(a(1)(0) == 0)
  }
}
