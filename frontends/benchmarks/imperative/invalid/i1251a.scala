import stainless._
import stainless.lang._

object i1251a {

  case class Box(var length: Int)

  def mutate(b: Box): Unit = { b.length = 123; }

  def h1(b1: Box, b2: Box, cond: Boolean): Unit = {
    val x = b1.length
    val c = if (cond) b1 else b2
    mutate(c)
    assert(b1.length == x)
  }
}
