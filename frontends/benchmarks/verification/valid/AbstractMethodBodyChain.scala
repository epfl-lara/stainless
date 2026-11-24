import stainless.lang._

// An abstract subclass may refine the contract of an inherited abstract method with
// another `AbstractMethodBody()`. Only the concrete class at the bottom implements it.
object AbstractMethodBodyChain {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      AbstractMethodBody[BigInt]()
    }.ensuring(_ >= 0)
  }

  abstract class NonEmptyShape extends Shape {
    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      AbstractMethodBody[BigInt]()
    }.ensuring(_ >= k)
  }

  case class Square(side: BigInt) extends NonEmptyShape {
    require(side >= 1)

    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      k + side
    }.ensuring(_ >= k)
  }

  def areaOfTwo(s: NonEmptyShape): BigInt = {
    s.area(2)
  }.ensuring(_ >= 2)

  def test: BigInt = {
    areaOfTwo(Square(2))
  }.ensuring(_ >= 2)
}
