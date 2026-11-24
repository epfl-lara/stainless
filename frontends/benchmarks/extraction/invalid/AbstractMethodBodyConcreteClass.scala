import stainless.lang._

// Counterpart of issue #1956: a concrete class cannot have abstract methods,
// even when the method overrides an abstract one.
object AbstractMethodBodyConcreteClass {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      AbstractMethodBody[BigInt]()
    }.ensuring(_ >= 0)
  }

  class GoodShape extends Shape {
    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      AbstractMethodBody[BigInt]()
    }.ensuring(_ >= 0)
  }

  def testMe: BigInt = {
    val s = new GoodShape
    s.area(0)
  }
}
