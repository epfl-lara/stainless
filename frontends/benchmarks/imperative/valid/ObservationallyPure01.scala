
object ObservationallyPure01 {
  def impureFunction(x: BigInt): BigInt = {
    x + 1
  }

  def pureFunction(x: BigInt): BigInt = {
    x + 1
  }
}