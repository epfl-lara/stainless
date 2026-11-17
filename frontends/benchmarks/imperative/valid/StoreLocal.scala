import stainless.lang._

object StoreLocal {
  case class Box(var value: BigInt)

  def f(m: MutableMap[BigInt, Box]): Unit = {
    val b = Box(1)
    m(0) = b

    b.value = 2

    assert(m(0).value == 2)
  }
}
