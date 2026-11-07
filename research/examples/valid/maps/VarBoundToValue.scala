import stainless.lang._

object VarBoundToValue {
  case class Box(var value: BigInt)

  def f(m: MutableMap[BigInt, Box]): Unit = {
    var x = m(0)

    x.value = 3

    assert(m(0).value == 3)
  }
}
