import stainless.lang._

// Local functions and first-class functions cannot be overridden either.
object AbstractMethodBodyLocalFunction {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      def inner(y: BigInt): BigInt = AbstractMethodBody[BigInt]()
      inner(k)
    }
  }
}
