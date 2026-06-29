import stainless.lang._

object BitVectorBigIntConversions {

  // `bigIntToInt` wraps around modulo 2^32, so this round-trip is lossy
  // (counterexample: any BigInt outside the Int range).
  def lossyRoundTrip(i: BigInt): Boolean = {
    bitVectorToBigInt(bigIntToInt(i)) == i
  }.holds

  // A bitvector value can be negative.
  def alwaysNonNeg(x: Int): Boolean = {
    bitVectorToBigInt(x) >= 0
  }.holds
}
