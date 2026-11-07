import stainless.lang._

object WriteOverStoredOtherIndexWrong {
  case class Box(var value: BigInt)

  def f(a: Array[Box], i: Int, k: Int): Unit = {
    require(0 <= i && i < a.length && k == i)

    val b = Box(1)
    a(i) = b

    a(k) = Box(2)
    b.value = 5

    assert(a(i).value == 2)
  }
}
