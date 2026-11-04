import stainless.lang._

object MapCalleeWriteThenMutateAlias {
  case class Box(var value: BigInt)

  def set(m: MutableMap[BigInt, Box]): Unit = {
    m(0) = Box(1)
  }

  def f(m: MutableMap[BigInt, Box]): Unit = {
    val x = m(0)
    set(m)

    x.value = 5

    assert(m(0).value == 5)
  }
}
