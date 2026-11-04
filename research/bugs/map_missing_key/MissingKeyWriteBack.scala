import stainless.lang._

object MissingKeyWriteBack {
  case class Box(var value: BigInt)

  def f: Unit = {
    val m = MutableMap.withDefaultValue[BigInt, Box](() => Box(0))
    val x = m(0)

    x.value = 1

    assert(m(0).value == 1)
  }
}
