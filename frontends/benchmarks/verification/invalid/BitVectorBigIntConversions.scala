import stainless.lang._

object BitVectorBigIntConversions {

  // `_.toInt` wraps around modulo 2^32, so this round-trip is lossy
  // (counterexample: any BigInt outside the Int range).
  def lossyRoundTrip(i: BigInt): Boolean = {
    BigInt(i.toInt) == i
  }.holds

  // A bitvector value can be negative.
  def alwaysNonNeg(x: Int): Boolean = {
    BigInt(x) >= 0
  }.holds
}
