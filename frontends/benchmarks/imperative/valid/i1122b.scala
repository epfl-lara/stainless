import stainless._
import stainless.lang._

object i1122b {

  // Like i1122a, but we pattern-match instead of "if-then-elsing"
  sealed trait Scrut
  case class Case1(x: BigInt) extends Scrut
  case class Case2(x: BigInt, y: BigInt) extends Scrut
  case class Case3(abc: BigInt) extends Scrut

  case class A(var x: BigInt)
  def reset(a: A): Unit = { a.x = 0 }

  def f(scrut: Scrut, a1: A, a2: A, a3: A): Unit = {
    val olda1x = a1.x
    val olda2x = a2.x
    val olda3x = a3.x
    reset(scrut match {
      case Case1(x) => a1
      case Case2(x, y) if x + y == 42 => a2
      case _ => a3
    })

    assert(scrut match {
      case Case1(x) =>
        a1.x == 0 && a2.x == olda2x && a3.x == olda3x
      case Case2(x, y) if x + y == 42 =>
        a1.x == olda1x && a2.x == 0 && a3.x == olda3x
      case _ =>
        a1.x == olda1x && a2.x == olda2x && a3.x == 0
    })
  }
}