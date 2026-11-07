import stainless.lang._

object ImmutableValues {
  def f(m: MutableMap[BigInt, BigInt]): Unit = {
    val x = m(0)
    m(0) = x
    val c = m.updated(0, 1)

    m(0) = 7

    assert(c(0) == 1)
  }
}
