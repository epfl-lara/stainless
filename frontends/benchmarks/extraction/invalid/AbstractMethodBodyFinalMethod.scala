import stainless.lang._

// Final and private methods cannot be overridden, so they cannot be abstract.
object AbstractMethodBodyFinalMethod {
  abstract class Shape {
    final def area(k: BigInt): BigInt = {
      require(k >= 0)
      AbstractMethodBody[BigInt]()
    }.ensuring(_ >= 0)

    private def secret: BigInt = {
      AbstractMethodBody[BigInt]()
    }.ensuring(_ >= 0)

    def reveal: BigInt = secret
  }

  case class Square(side: BigInt) extends Shape
}
