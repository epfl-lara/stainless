import stainless.lang._

// Anonymous and local classes implementing the abstract method are fine too.
object AbstractMethodBodyAnonymousImpl {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      AbstractMethodBody[BigInt]()
    }.ensuring(_ >= 0)
  }

  def anonymous(side: BigInt): Shape = {
    require(side >= 0)
    new Shape {
      override def area(k: BigInt): BigInt = {
        require(k >= 0)
        k + side
      }.ensuring(_ >= 0)
    }
  }

  def local(side: BigInt): BigInt = {
    require(side >= 0)
    case class Local() extends Shape {
      override def area(k: BigInt): BigInt = {
        require(k >= 0)
        k + side
      }.ensuring(_ >= 0)
    }
    Local().area(1)
  }.ensuring(_ >= 0)

  def test: BigInt = {
    anonymous(2).area(3) + local(2)
  }.ensuring(_ >= 0)
}
