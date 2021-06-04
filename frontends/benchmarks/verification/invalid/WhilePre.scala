import stainless.lang._

object WhilePre {
  def f(n: BigInt): Unit = {
    var i = n
    (while (i > 0) {
      decreases(i)
      i -= 1
    }).inline.opaque.invariant(n == 5)
  }
}
