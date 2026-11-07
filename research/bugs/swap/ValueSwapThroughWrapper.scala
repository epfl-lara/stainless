import stainless.lang._

object ValueSwapThroughWrapper {
  case class Box(var value: BigInt)

  def wrapper(c1: Cell[Box], c2: Cell[Box]): Unit = {
    swap(c1, c2)
  }

  def f: Unit = {
    val a = Cell(Box(0))
    val b = Box(1)

    {
      val c = Cell(b)
      wrapper(a, c)
    }

    assert(a.v.value == 1)

    b.value = 3

    assert(a.v.value == 1)
  }
}
