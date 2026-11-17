import stainless.lang._

object AliasWithPartialMutation {
  case class Point(var x: BigInt, var y: BigInt)

  def f: Unit = {
    var a = Point(4, 1)
    var b = a

    a.x = 2
    a.y = 9

    assert(b.x == 2)
    assert(b.y == 9)
  }
}
