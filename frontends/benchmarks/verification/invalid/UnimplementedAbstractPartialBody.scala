import stainless.lang._

// `???` in a part of a body that the concrete class inherits and runs.
object UnimplementedAbstractPartialBody {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      if (k == 0) BigInt(0) else (??? : BigInt)
    }.ensuring(_ >= 0)
  }

  case class Square(side: BigInt) extends Shape

  def test: BigInt = {
    Square(2).area(1)
  }.ensuring(_ >= 0)
}
