import stainless.lang._

object SimpleReassignNoAliasing {
  case class Box(var value: BigInt)

  def f: Unit = {
    var a = Box(4)

    a = Box(5)

    assert(a.value == 5)
  }
}
