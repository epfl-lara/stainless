import stainless.lang._

object ValueSwapCellVar {
  case class Box(var value: BigInt)

  def f: Unit = {
    val a = Box(1)
    var c = Cell(a)

    assert(c.v.value == 1)

    a.value = 3

    assert(c.v.value == 3)
  }
}
