import stainless._
import stainless.lang._

object i1122a {
  case class A(var x: BigInt)
  def reset(a: A): Unit = { a.x = 0 }

  def f(cond: Boolean, a1: A, a2: A): Unit = {
    val olda1x = a1.x
    val olda2x = a2.x
    reset(if (cond) a1 else a2)
    assert(cond ==> (a1.x == 0 && a2.x == olda2x))
    assert(!cond ==> (a1.x == olda1x && a2.x == 0))
  }
}