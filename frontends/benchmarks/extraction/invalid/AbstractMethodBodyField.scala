import stainless.lang._

// The initialiser of a field runs when an instance is created, even when a
// subclass overrides the field: it cannot be abstract that way.
object AbstractMethodBodyField {
  abstract class Shape {
    val sides: BigInt = AbstractMethodBody[BigInt]()
  }

  case class Square(override val sides: BigInt) extends Shape
}
