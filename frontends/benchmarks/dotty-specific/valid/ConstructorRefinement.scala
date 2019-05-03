import stainless.lang._

object ConstructorRefinement {

  case class Rectangle(
    x: { x: BigInt => x >= BigInt(0) },
    y: { y: BigInt => y >= BigInt(0) }
  )

  def (r: Rectangle) perimeter: BigInt = r.x * 2 + r.y * 2

  def test(rectangle: Rectangle) = {
    assert(rectangle.perimeter >= 0)
  }

}
