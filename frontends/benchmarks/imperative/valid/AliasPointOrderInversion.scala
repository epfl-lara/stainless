import stainless.lang._

object AliasPointOrderInversion {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)
  case class Outer(h: Holder)

  def f: Unit = {
    val a = Box(4)
    val h = Holder(Box(0))
    val o = Outer(h)

    h.b = a

    assert(h.b.value == 4)
    assert(o.h.b.value == 4)

    a.value = 99

    assert(a.value == 99)
    assert(h.b.value == 99)
    assert(o.h.b.value == 99)
  }
}
