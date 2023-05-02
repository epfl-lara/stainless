import stainless.lang._

object BadAliasing3 {
  case class A(var x: BigInt)
  case class Box(var boxed: A)

  def h(m: Map[BigInt, A], a: A) = {
    val m2 = m.updated(0, a)
    a.x = 0
    assert(m2(0).x == 0)
  }
}
