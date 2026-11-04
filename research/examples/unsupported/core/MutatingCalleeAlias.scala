import stainless.lang._

object MutatingCalleeAlias {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)

  def setAndGet(h: Holder, a: Box): Box = {
    h.b = a
    h.b
  }

  def f(a: Box, b: Box): Unit = {
    val h = Holder(a)
    val m = setAndGet(h, b)

    m.value = 1

    assert(b.value == 1)
  }
}
