import stainless.lang._

object MapWriteInBranchThenMutateAlias {
  case class Box(var value: BigInt)

  def f(m: MutableMap[BigInt, Box], k: BigInt, c: Boolean): Unit = {
    val x = m(k)
    if (c) m(k) = Box(1)

    x.value = 2

    assert(m(k).value == 2)
  }
}
