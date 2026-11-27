import stainless.lang._

object PrecondWitnessInvalid1 {
  // The arguments of the witness don't satisfy the precondition
  def f(x: BigInt): BigInt = {
    require(x >= 0)
    precondWitness(f(-2))
    2 * x
  }.ensuring(res => res == x * 2)
}
