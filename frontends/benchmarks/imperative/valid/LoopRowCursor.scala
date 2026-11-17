import stainless.lang._

object LoopRowCursor {
  def f(a: Array[Array[BigInt]]): Unit = {
    require(a.length > 0 && a(0).length > 0)

    var k = 0
    (while (k < a.length) {
      decreases(a.length - k)
      val row = a(k)
      if (row.length > 0) {
        row(0) = 1
      }
      k += 1
    }).invariant(0 <= k && k <= a.length && a.length > 0 && a(0).length > 0 && (k == 0 || a(0)(0) == 1))

    assert(a(0)(0) == 1)
  }
}
