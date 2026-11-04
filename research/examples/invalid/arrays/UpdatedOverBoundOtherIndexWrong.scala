import stainless.lang._

object UpdatedOverBoundOtherIndexWrong {
  case class Box(var value: BigInt)

  def f: Unit = {
    var a = Array(Box(1), Box(2))
    val k = 0
    val x = a(0)

    a = a.updated(k, Box(9))
    x.value = 5

    assert(a(0).value == 9)
  }
}
