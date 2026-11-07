import stainless.lang._

object AliasMultiLevelVar {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)
  case class Outer(var h: Holder)

  def f: Unit = {
    var a = Box(4)
    var h = Holder(a)
    var o = Outer(h)

    a.value = 5

    assert(a.value == 5)
    assert(h.b.value == 5)
    assert(o.h.b.value == 5)

    h.b = Box(1)

    assert(a.value == 5)
    assert(h.b.value == 1)
    assert(o.h.b.value == 1)

    o.h = Holder(Box(2))

    assert(a.value == 5)
    assert(h.b.value == 1)
    assert(o.h.b.value == 2)
  }
}
