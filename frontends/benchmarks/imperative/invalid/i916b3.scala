import stainless._
import stainless.lang._

object i916b3 {
  case class A(var a: BigInt)

  def f(b1: Boolean, b2: Boolean) = {
    val a1 = A(1)
    val a2 = A(2)
    val a3 = A(3)
    val x = if (b1) (if (b2) a1 else a2) else a3
    x.a = 42

    // This assertion should fail.
    // We are testing whether AntiAliasing has correctly "updated" a1.
    assert(a1.a == 1)
  }
}
