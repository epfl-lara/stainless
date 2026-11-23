import stainless.lang._

// The concrete classes and the object do not implement the abstract method. Scala accepts
// them because `area` has a body, but calling it would crash at run time.
object AbstractMethodBodyMissingOverride {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      AbstractMethodBody[BigInt]()
    }.ensuring(_ >= 0)
  }

  case class Square(side: BigInt) extends Shape

  case object Origin extends Shape

  def test: BigInt = {
    Square(2).area(1) + Origin.area(1)
  }.ensuring(_ >= 0)
}
