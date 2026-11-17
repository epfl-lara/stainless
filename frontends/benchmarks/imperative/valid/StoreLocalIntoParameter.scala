import stainless.lang._

object StoreLocalIntoParameter {
  case class Box(var value: BigInt)

  def f(a: Array[Box]): Unit = {
    require(a.length > 0)

    val b = Box(1)
    a(0) = b

    b.value = 2

    assert(a(0).value == 2)
  }
}
