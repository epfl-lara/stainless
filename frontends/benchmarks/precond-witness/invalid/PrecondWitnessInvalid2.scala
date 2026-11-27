import stainless.lang._

object PrecondWitnessInvalid2 {
  // The second precondition does not hold for the arguments of the witness
  def f(x: BigInt, y: BigInt): BigInt = {
    require(x >= 0)
    require(y > x)
    precondWitness({
      val a = BigInt(3)
      f(a, a)
    })
    y - x
  }.ensuring(res => res > 0)
}
