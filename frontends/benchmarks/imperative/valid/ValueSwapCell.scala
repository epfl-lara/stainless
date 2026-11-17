import stainless.lang._

object ValueSwapCell {
  case class Box(var value: BigInt)

  def f: Unit = {
    val a = Box(1)
    val c = Cell(a)

    assert(c.v.value == 1)

    a.value = 3

    assert(c.v.value == 3)
  }
}
