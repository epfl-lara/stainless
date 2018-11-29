import stainless.lang._

object MutableMapUpdated {
  case class A(var x: BigInt)

  def f(m: MutableMap[BigInt,A], a: A) = {
    // not allowed due to the creation of aliases between `m` and the result
    val u = m.updated(0, a)
    ()
  }
}
