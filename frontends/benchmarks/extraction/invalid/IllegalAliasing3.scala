import stainless._
import stainless.lang._

object IllegalAliasing3 {
  case class A(var a: BigInt)

  def f(b1: Boolean) = {
    val a1 = A(1)
    val a2 = A(2)
    // Illegal aliasing
    var x = if (b1) a1 else a2
    x.a = 42
  }
}
