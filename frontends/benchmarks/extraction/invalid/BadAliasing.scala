import stainless.lang._

object BadAliasing {
  case class A(var x: BigInt)
  case class Box(var boxed: A)

  def f(m: Box, a: A) = {
    m.boxed = a
    a.x = 0
    assert(m.boxed.x == 0)
  }

  def g(m: Array[A], a: A) = {
    require(m.length > 0)
    m(0) = a
    a.x = 0
    assert(m(0).x == 0)
  }

  def h(m: Map[BigInt, A], a: A) = {
    val m2 = m.updated(0, a)
    a.x = 0
    assert(m2(0).x == 0)
  }
}
