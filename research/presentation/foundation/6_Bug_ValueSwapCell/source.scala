import stainless.lang._
import stainless.annotation._

case class X(var x: BigInt)

object ValueSwapCell {
  def simplerUnsoundExampleCell(): Unit = {
    val a = Cell[X](X(0))
    val newV = X(1)
    swap(a, Cell(newV))
    assert(a.v.x == 1)
    newV.x = 3
    assert(a.v.x == 1) // BUG: should be 3
  }
}
