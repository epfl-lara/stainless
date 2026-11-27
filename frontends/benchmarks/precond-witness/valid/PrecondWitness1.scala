import stainless.lang._

object PrecondWitness1 {
  def f(x: BigInt): BigInt = {
    require(x >= 0)
    precondWitness(f(2))
    2 * x
  }.ensuring(res => res == x * 2)
}
