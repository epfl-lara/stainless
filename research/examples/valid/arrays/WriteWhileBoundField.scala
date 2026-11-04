import stainless.lang._

object WriteWhileBoundField {
  case class Box(var value: BigInt)

  case class Holder(b: Box)

  def f(a: Array[Box], i: Int): Unit = {
    require(0 <= i && i < a.length)

    val h = Holder(a(i))

    a(i) = Box(3)
    h.b.value = 1
  }
}
