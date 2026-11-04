import stainless.lang._

object StoreThenMutateThroughOtherIndex {
  case class Box(var value: BigInt)

  def f(a: Array[Box], i: Int, k: Int): Unit = {
    require(0 <= i && i < a.length && k == i)

    val b = Box(1)
    a(i) = b

    a(k).value = 2

    assert(b.value == 2)
  }
}
