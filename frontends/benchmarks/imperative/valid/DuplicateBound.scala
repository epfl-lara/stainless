import stainless.lang._

object DuplicateBound {
  case class Box(var value: BigInt)

  def f: Unit = {
    val m = MutableMap.withDefaultValue[BigInt, Box](() => Box(0))
    val x = m(0)
    val c = m.duplicate()

    x.value = 5

    assert(x.value == 5)
    assert(c(0).value == 5)
  }
}
