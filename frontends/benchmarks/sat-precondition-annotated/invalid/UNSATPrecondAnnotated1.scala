import stainless.annotation._

object UNSATPrecondAnnotated1 {
  // Checked: its precondition is unsatisfiable
  @checkSatPrecondition
  def f(x: BigInt): BigInt = {
    require(x > 0)
    require(x < 0)
    x
  }

  // Not annotated
  def g(x: BigInt): BigInt = {
    require(x > 0)
    x
  }
}
