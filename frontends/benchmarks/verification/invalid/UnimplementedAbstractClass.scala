import stainless.lang._

// `???` is not the way to write an abstract method: it must be unreachable even
// when all the concrete subclasses override the method. See `AbstractMethodBody()`.
object UnimplementedAbstractClass {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      (??? : BigInt)
    }.ensuring(_ >= 0)
  }

  case class Square(side: BigInt) extends Shape {
    require(side >= 0)

    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      k + side
    }.ensuring(_ >= 0)
  }
}
