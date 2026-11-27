import stainless.lang._

object PrecondWitness2 {
  // The arguments of the witness can be computed in a block
  def f(x: BigInt): BigInt = {
    require(x >= 0)
    precondWitness({
      val z = 2 * 2
      val r = z * 2
      f(z + r)
    })
    2 * x
  }.ensuring(res => res == x * 2)
}
