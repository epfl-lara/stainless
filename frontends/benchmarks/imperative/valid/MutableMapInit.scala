import stainless.lang._

object MutableMapInit {

  case class A(var x: BigInt)

  def f() = {
    val m = MutableMap.withDefaultValue[BigInt, A](() => A(5))
    assert(m(0).x == 5)
    m(0).x = 6
    assert(m(0).x == 6)
    assert(m(1).x == 5)
    m(1).x = 8
    assert(m(1).x == 8)
    assert(m(0).x == 6)
  }
}
