import stainless.lang._

object MutableInstantiationSet {
  case class Box(var value: BigInt)

  def f(b: Box): Boolean = {
    val s: Set[Box] = Set(b)
    s.contains(b)
  }
}
