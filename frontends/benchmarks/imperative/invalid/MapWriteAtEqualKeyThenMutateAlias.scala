import stainless.lang._

object MapWriteAtEqualKeyThenMutateAlias {
  case class Box(var value: BigInt)

  def f(m: MutableMap[BigInt, Box], j: BigInt, k: BigInt): Unit = {
    require(j == k)

    val x = m(j)
    m(k) = Box(3)

    x.value = 1

    assert(m(j).value == 1)
  }
}
