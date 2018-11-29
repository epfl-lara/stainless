import stainless.lang._

object MutableMapUpdated {
  def f(m: MutableMap[BigInt, BigInt]) = {
    val m1 = m.duplicate
    m(0) = 5
    assert(m == m1.updated(0,5))
  }
}