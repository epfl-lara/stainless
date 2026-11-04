import stainless.lang._

object UpdatedSelfLocal {
  case class Box(var value: BigInt)

  def f: Unit = {
    var m = MutableMap.withDefaultValue[BigInt, Box](() => Box(0))
    m = m.updated(0, Box(1))

    m(1).value = 3

    assert(m(1).value == 3)
    assert(m(0).value == 1)
  }
}
