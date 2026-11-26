import stainless.lang._

// `AbstractMethodBody()` stands for a whole body, not for a part of it.
object AbstractMethodBodySubExpression {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      if (k == 0) BigInt(0) else AbstractMethodBody[BigInt]()
    }.ensuring(_ >= 0)
  }

  case class Point() extends Shape {
    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      BigInt(0)
    }.ensuring(_ >= 0)
  }
}
