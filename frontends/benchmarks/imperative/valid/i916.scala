import stainless._
import stainless.lang._

object i916 {
  case class A(var a: BigInt)

  def f1(b1: Boolean) = {
    val a1 = A(1)
    val a2 = A(2)
    val x = if (b1) a1 else a2
    x.a = 42

    val xyz = x
    assert(b1 ==> (a1.a == 42 && a2.a == 2))
    assert(!b1 ==> (a1.a == 1 && a2.a == 42))
    assert(x.a == 42)
    assert(xyz.a == 42)
  }

  def f2(b1: Boolean, b2: Boolean) = {
    val a1 = A(1)
    val a2 = A(2)
    val a3 = A(3)
    val x = if (b1) (if (b2) a1 else a2) else a3
    x.a = 42

    val xyz = x
    assert((b1 && b2) ==> (a1.a == 42 && a2.a == 2 && a3.a == 3))
    assert((b1 && !b2) ==> (a1.a == 1 && a2.a == 42 && a3.a == 3))
    assert(!b1 ==> (a1.a == 1 && a2.a == 2 && a3.a == 42))
    assert(x.a == 42)
    assert(xyz.a == 42)
  }
}
