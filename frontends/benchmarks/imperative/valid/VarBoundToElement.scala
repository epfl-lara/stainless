import stainless.lang._

object VarBoundToElement {
  case class Box(var value: BigInt)

  def f(a: Array[Box]): Unit = {
    require(a.length > 0)

    var x = a(0)

    x.value = 0

    assert(a(0).value == 0)
  }

  def g(a: Array[Box]): Unit = {
    require(a.length > 0)

    f(a)

    assert(a(0).value == 0)
  }
}
