import stainless.lang._

object AliasKillMechanismVar {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)

  def f: Unit = {
    var a = Box(4)
    var h = Holder(a)

    h.b = Box(1)

    assert(h.b.value == 1)

    a.value = 99

    assert(a.value == 99)
    assert(h.b.value == 1)
  }
}
