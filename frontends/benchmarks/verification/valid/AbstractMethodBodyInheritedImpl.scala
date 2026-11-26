import stainless.lang._

// A concrete class does not have to override the method itself when one of its
// ancestors already implements it. A `super` call reaching that implementation is fine.
object AbstractMethodBodyInheritedImpl {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      AbstractMethodBody[BigInt]()
    }.ensuring(_ >= 0)
  }

  abstract class Flat extends Shape {
    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      BigInt(0)
    }.ensuring(_ >= 0)
  }

  case class Point() extends Flat

  case class Segment(length: BigInt) extends Flat {
    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      super.area(k) + 0
    }.ensuring(_ >= 0)
  }

  def test: BigInt = {
    val p: Shape = Point()
    p.area(1) + Segment(3).area(1)
  }.ensuring(_ >= 0)
}
