import stainless.annotation._

object UNSATPrecondAnnotated2 {
  case class Counter(value: BigInt) {
    // Methods can be annotated too
    @checkSatPrecondition
    def add(n: BigInt): Counter = {
      require(n >= 0 && n < 0)
      Counter(value + n)
    }
  }
}
