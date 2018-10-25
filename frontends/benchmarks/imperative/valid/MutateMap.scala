import stainless.lang._

object MutateMap {

  case class A(var x: BigInt)

  def f(m: MutableMap[BigInt, A], a: A) = {
    require(a.x == 100)
    m(0) = a
    assert(m(0).x == 100)
  }

}
