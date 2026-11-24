import stainless.lang._

// The initialiser of a field of an abstract class runs when an instance of a subclass
// is created, even when the subclass overrides the field: its assertions must hold.
object FieldInitializerAbstractClass {
  abstract class Shape {
    val sides: BigInt = { assert(false); BigInt(3) }
  }

  case class Square(override val sides: BigInt) extends Shape
}
