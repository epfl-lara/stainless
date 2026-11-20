import stainless.lang._
import stainless.annotation._

object MutableTypeParameter {
  case class Box(var value: BigInt)
  case class Cell[@mutable T](v: T)

  def f(b: Box): Unit = {
    val c = Cell(b)

    c.v.value = 1

    assert(b.value == 1)
  }
}
