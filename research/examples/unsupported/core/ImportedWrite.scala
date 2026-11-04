import stainless.lang._

object ImportedWrite {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)

  def set(h: Holder, a: Box): Unit = {
    h.b = a
  }

  def f(a: Box, b: Box): Unit = {
    val h = Holder(a)

    set(h, b)
    b.value = 1

    assert(h.b.value == 1)
  }
}
