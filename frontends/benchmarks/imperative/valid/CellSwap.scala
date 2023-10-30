import stainless.lang.swap
import stainless.lang.Cell

object CellSwap {
  def test(c1: Cell[Int], c2: Cell[Int]): Unit = {
    require(c1.v == 1 && c2.v == 2)

    swap(c1, c2)
    assert(c1.v == 2)
    assert(c2.v == 1)
    swap(c1, c1)
    assert(c1.v == 2)
    c1.v = 42
    assert(c1.v == 42)
    swap(c1, c2)
    assert(c1.v == 1)
    assert(c2.v == 42)
  }

}
