import stainless.lang._

object UpdatedSelfLocal {
  case class Box(var value: BigInt)

  def f: Unit = {
    var a = Array(Box(1), Box(2))

    a = a.updated(0, Box(0))
    a(1).value = 3

    assert(a(1).value == 3)
  }
}
