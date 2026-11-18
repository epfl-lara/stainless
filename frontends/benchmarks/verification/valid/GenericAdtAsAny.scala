import stainless.lang._

object GenericAdtAsAny {
  sealed abstract class Shape[V]
  case class Labeled[V](label: V) extends Shape[V]

  // Values of generic ADTs are converted to `Any` along with the values of their type parameters
  def toAny[V](s: Shape[V]): Any = s

  def test: Unit = {
    assert(toAny(Labeled(BigInt(1))) == toAny(Labeled(BigInt(1))))
  }
}
