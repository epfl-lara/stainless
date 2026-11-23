import stainless.lang._

// Final and private methods of an abstract class cannot be overridden either,
// so their `???` body is the code that runs.
object UnimplementedFinalMethod {
  abstract class Shape {
    final def area(k: BigInt): BigInt = {
      require(k >= 0)
      (??? : BigInt)
    }.ensuring(_ >= 0)

    private def secret: BigInt = {
      (??? : BigInt)
    }.ensuring(_ >= 0)

    def reveal: BigInt = secret
  }

  case class Square(side: BigInt) extends Shape

  def test: BigInt = {
    Square(2).area(1) + Square(2).reveal
  }.ensuring(_ >= 0)
}
