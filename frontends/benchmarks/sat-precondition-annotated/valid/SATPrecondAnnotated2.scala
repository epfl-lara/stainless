import stainless.annotation._

object SATPrecondAnnotated2 {
  case class Counter(value: BigInt) {
    // Methods can be annotated too
    @checkSatPrecondition
    def add(n: BigInt): Counter = {
      require(n >= 0 && value >= 0)
      Counter(value + n)
    }.ensuring(_.value >= value)
  }
}
