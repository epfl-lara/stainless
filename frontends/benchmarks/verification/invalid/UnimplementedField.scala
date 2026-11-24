import stainless.lang._

// The initialiser of a field runs when an instance is created, even when a
// subclass overrides the field: `Square(4)` crashes in the constructor of `Shape`.
object UnimplementedField {
  abstract class Shape {
    val sides: BigInt = (??? : BigInt)
  }

  case class Square(override val sides: BigInt) extends Shape

  def test: BigInt = {
    Square(4).sides
  }.ensuring(_ == 4)
}
