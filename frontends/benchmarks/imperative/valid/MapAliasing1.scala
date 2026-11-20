import stainless.lang._

object MapAliasing1 {

  case class A(var x: BigInt)

  def f(m: MutableMap[BigInt, A], n: Int): A = {
    m(0).x += 10
    m(0)
  }

  def test1 = {
    val m = MutableMap.withDefaultValue[BigInt, A](() => A(0))

    m(0) = A(32)

    val a = f(m, 123)
    a.x += 1

    assert(m(0).x == 43)
  }
}
