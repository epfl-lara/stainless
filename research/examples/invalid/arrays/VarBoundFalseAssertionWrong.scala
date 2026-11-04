import stainless.lang._

object VarBoundFalseAssertionWrong {
  case class Box(var value: BigInt)

  def f(a: Array[Box]): Unit = {
    require(a.length > 0 && a(0).value == 1)

    var x = a(0)

    x.value = 0

    assert(a(0).value == 1)
  }
}
