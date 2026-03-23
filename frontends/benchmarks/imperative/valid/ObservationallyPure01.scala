import stainless.annotation.observationallyPure

object ObservationallyPure01 {
  @observationallyPure("pureFunction")
  def impureFunction(x: BigInt): BigInt = {
    x + 1
  }

  def pureFunction(x: BigInt): BigInt = {
    x + 1
  }
}