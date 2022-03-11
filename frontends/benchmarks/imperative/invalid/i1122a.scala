import stainless._
import stainless.lang._

object i1122a {
  case class A(var x: BigInt)
  def reset(a: A): Unit = { a.x = 0 }

  def f(cond: Boolean, a1: A, a2: A): Unit = {
    reset(if (cond) a1 else a2)
    // Both assertions are wrong
    assert(a1.x == 0)
    assert(a2.x == 0)
  }
}