import stainless.lang._

object MutateMapElement {

  case class A(var x: BigInt)

  def f(m: MutableMap[BigInt, MutableMap[BigInt, A]]) = {
    m(0)(0).x = 100
    assert(m(0)(0).x == 100)
  }
}
