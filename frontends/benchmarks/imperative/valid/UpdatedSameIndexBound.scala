import stainless.lang._

object UpdatedSameIndexBound {
  case class Box(var value: BigInt)

  def f: Unit = {
    var a = Array(Box(1), Box(2))
    val x = a(0)

    a = a.updated(0, Box(9))
    x.value = 5

    assert(x.value == 5)
    assert(a(0).value == 9)
  }
}
