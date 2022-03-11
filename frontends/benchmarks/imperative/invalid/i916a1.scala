import stainless._
import stainless.lang._

object i916a1 {
  case class A(var a: BigInt)

  def f(b1: Boolean) = {
    val a1 = A(1)
    val a2 = A(2)
    val x = if (b1) a1 else a2
    x.a = 42

    val xyz = x
    // This assertion should fail.
    // We are testing whether AntiAliasing is correctly using the "updated" value of x and not the
    // original `val x = if (b1) a1 else a2`
    assert(b1 ==> (xyz.a == 1))
  }
}
