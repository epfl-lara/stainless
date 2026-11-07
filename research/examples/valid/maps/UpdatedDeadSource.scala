import stainless.lang._

object UpdatedDeadSource {
  case class Box(var value: BigInt)

  def f: Unit = {
    val m = MutableMap.withDefaultValue[BigInt, Box](() => Box(0))
    val c = m.updated(0, Box(1))

    c(0).value = 3

    assert(c(0).value == 3)
  }
}
