import stainless.lang._

// The concrete classes and the object inherit the `???` body: Scala accepts them
// because `area` has a body, but calling it crashes at run time.
object UnimplementedMissingOverride {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      (??? : BigInt)
    }.ensuring(_ >= 0)
  }

  case class Square(side: BigInt) extends Shape

  case object Origin extends Shape

  def test: BigInt = {
    Square(2).area(1) + Origin.area(1)
  }.ensuring(_ >= 0)
}
