import stainless.lang._

object BadAliasing1 {
  case class A(var x: BigInt)
  case class Box(var boxed: A)

  def f(m: Box, a: A) = {
    m.boxed = a
    a.x = 0
    assert(m.boxed.x == 0)
  }
}
