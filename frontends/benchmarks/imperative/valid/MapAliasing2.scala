import stainless.lang._

object MapAliasing2 {

  case class A(var x: BigInt)

  def f(m: MutableMap[BigInt, A], n: Int): A = {
    m(0).x += 10
    m(0)
  }

  def test2(m: MutableMap[BigInt, A])  = {
    require(m(0) == A(32))

    val a = f(m, 123)
    val b = f(m, 456)

    a.x += 1

    assert(m(0).x == 53)
    assert(b.x == 53)
  }

}
