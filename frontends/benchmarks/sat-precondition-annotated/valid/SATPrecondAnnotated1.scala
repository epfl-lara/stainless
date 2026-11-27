import stainless.annotation._

object SATPrecondAnnotated1 {
  // Checked: its precondition is satisfiable
  @checkSatPrecondition
  def f(x: BigInt): BigInt = {
    require(x > 0)
    x
  }

  // Not annotated, so its unsatisfiable precondition is not checked with --sat-precond=annotated
  def g(x: BigInt): BigInt = {
    require(x > 0)
    require(x < 0)
    x
  }
}
