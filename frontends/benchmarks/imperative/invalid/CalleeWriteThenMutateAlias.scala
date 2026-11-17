import stainless.lang._

object CalleeWriteThenMutateAlias {
  case class Box(var value: BigInt)

  def set(a: Array[Box]): Unit = {
    require(a.length > 0)
    a(0) = Box(1)
  }

  def f(a: Array[Box]): Unit = {
    require(a.length > 0 && a(0).value == 0)

    val x = a(0)
    set(a)

    x.value = 5

    assert(a(0).value == 5)
  }
}
