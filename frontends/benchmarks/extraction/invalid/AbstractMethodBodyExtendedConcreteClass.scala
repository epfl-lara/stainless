import stainless.lang._

// A concrete class cannot have abstract methods, even when it is extended:
// `new Shape` would run the body of `area`.
object AbstractMethodBodyExtendedConcreteClass {
  class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      AbstractMethodBody[BigInt]()
    }.ensuring(_ >= 0)
  }

  case class Square(side: BigInt) extends Shape {
    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      side * side
    }.ensuring(_ >= 0)
  }

  def testMe: BigInt = {
    val s = new Shape
    s.area(0)
  }
}
