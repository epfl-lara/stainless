import stainless.lang._

object BadAliasing2 {
  case class A(var x: BigInt)
  case class Box(var boxed: A)

  def g(m: Array[A], a: A) = {
    require(m.length > 0)
    m(0) = a
    a.x = 0
    assert(m(0).x == 0)
  }
}
