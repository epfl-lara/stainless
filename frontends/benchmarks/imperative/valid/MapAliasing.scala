import stainless.lang._

object MapAliasing {

  case class A(var x: BigInt)

  def f(m: MutableMap[BigInt, A], n: Int): A = {
    m(0)
  }

  def test1 = {
    val m = MutableMap.withDefaultValue[BigInt, A](() => A(0))

    m(0) = A(42)

    val a = f(m, 123)
    a.x += 1

    assert(m(0).x == 43)
  }

  def test2(m: MutableMap[BigInt, A])  = {
    require(m(0) == A(42))

    val a = f(m, 123)
    val b = f(m, 456)

    a.x += 1

    assert(m(0).x == 43)
    assert(b.x == 43)
  }

}
