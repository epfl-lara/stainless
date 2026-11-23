import stainless.lang._

// The override is a real implementation, but it calls the `???` body through `super`.
object UnimplementedSuperCall {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      (??? : BigInt)
    }.ensuring(_ >= 0)
  }

  case class Square(side: BigInt) extends Shape {
    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      super.area(k) + 1
    }.ensuring(_ >= 0)
  }

  def test: BigInt = {
    Square(2).area(1)
  }.ensuring(_ >= 0)
}
