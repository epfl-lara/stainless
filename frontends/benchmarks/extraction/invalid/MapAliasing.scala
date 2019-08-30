import stainless.lang._

object MapAliasing {

  case class A(var x: BigInt)

  def f(m: MutableMap[BigInt, A]): A = {
    m(0)
  }

}
