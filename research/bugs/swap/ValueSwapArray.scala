import stainless.lang._

object ValueSwapArray {
  case class Box(var value: BigInt)

  def f: Unit = {
    val a = Array(Box(0), Box(0), Box(0))
    val b = Box(1)

    swap(a, 0, Array(b), 0)

    assert(a(0).value == 1)

    b.value = 3

    assert(a(0).value == 1)
  }

  def g: Unit = {
    val a = Cell(Box(0))
    val b = Box(1)

    swap(a, Cell(b))

    assert(a.v.value == 1)

    b.value = 3

    assert(a.v.value == 1)
  }
}
