import stainless.lang._

// Example of issue #1956: a concrete class "implements" the method with `???`,
// so `testMe` crashes with a NotImplementedError at run time.
object UnimplementedConcreteOverride {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      (??? : BigInt)
    }.ensuring(_ >= 0)
  }

  class GoodShape extends Shape {
    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      (??? : BigInt)
    }.ensuring(_ >= 0)
  }

  def testMe: BigInt = {
    val s = new GoodShape
    s.area(0)
  }
}
