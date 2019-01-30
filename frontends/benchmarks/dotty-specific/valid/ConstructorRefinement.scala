
import stainless.lang._

object ExtensionMethods1 {

  case class Rectangle(
    x: { x: BigInt => x >= 0),
    y: { y: BigInt => y >= 0 }
  ) {
    def perimiter: BigInt = x * 2 + y * 2
  }

  def test(r: Rectangle) = {
    assert(rectangle.perimiter >= 0)
  }

}
