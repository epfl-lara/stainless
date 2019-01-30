
import stainless.lang._

object ExtensionMethods1 {

  case class Rectangle(x: BigInt, y: BigInt)

  def (r: Rectangle) perimeter: BigInt = r.x * 2 + r.y * 2

  def test = {
    val rectangle = Rectangle(10, 20)
    assert(rectangle.perimeter == 60)
  }

}
