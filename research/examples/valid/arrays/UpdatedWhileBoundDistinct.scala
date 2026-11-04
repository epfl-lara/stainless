import stainless.lang._

object UpdatedWhileBoundDistinct {
  case class Box(var value: BigInt)

  def f: Unit = {
    var a = Array(Box(1), Box(2))
    val x = a(1)

    a = a.updated(0, Box(0))
    x.value = 5

    assert(a(1).value == 5)
    assert(a(0).value == 0)
  }
}
