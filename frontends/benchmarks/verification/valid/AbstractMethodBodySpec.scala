import stainless.lang._

// `AbstractMethodBody()` as the body of a method of an abstract class gives a contract
// to an abstract method. Every concrete subclass must override it, so it never runs.
object AbstractMethodBodySpec {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      AbstractMethodBody[BigInt]()
    }.ensuring(_ >= 0)
  }

  case class Square(side: BigInt) extends Shape {
    require(side >= 0)

    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      k + side
    }.ensuring(_ >= 0)
  }

  case class Point() extends Shape {
    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      BigInt(0)
    }.ensuring(_ >= 0)
  }

  def scaledArea(s: Shape, k: BigInt): BigInt = {
    require(k >= 0)
    s.area(k)
  }.ensuring(_ >= 0)

  def test: BigInt = {
    scaledArea(Square(3), 2) + scaledArea(Point(), 2)
  }.ensuring(_ >= 0)
}
