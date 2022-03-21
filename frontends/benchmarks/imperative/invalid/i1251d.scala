import stainless._
import stainless.lang._

object i1251d {
  // Like i1251b, but we pattern-match instead of "if-then-elsing"
  sealed trait Scrut
  case class Case1(x: BigInt) extends Scrut
  case class Case2(x: BigInt, y: BigInt) extends Scrut
  case class Case3(abc: BigInt) extends Scrut

  case class Box(var length: Int)

  def mutate(b: Box): Unit = { b.length = 123; }

  def h1(b1: Box, b2: Box, b3: Box, scrut: Scrut): Unit = {
    val x = b1.length
    val c = scrut match {
      case Case1(x) => b1
      case Case2(x, y) if x + y == 42 => b2
      case _ => b3
    }
    val d = c
    mutate(d)
    assert(b1.length == x)
  }
}
