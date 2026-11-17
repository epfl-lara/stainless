import stainless.lang._

object LoopRowAlias {
  def f(a: Array[Array[BigInt]], n: BigInt): Unit = {
    require(a.length > 0 && a(0).length > 0 && n > 0)

    val row = a(0)
    var i = BigInt(0)
    (while (i < n) {
      decreases(n - i)
      row(0) = i
      i = i + 1
    }).invariant(0 <= i && i <= n && a.length > 0 && a(0).length > 0 && row.length > 0 && (i == 0 || a(0)(0) == i - 1))

    assert(a(0)(0) == n - 1)
  }
}
