import stainless.lang._

object BitVectorBigIntConversions {

  // `bitVectorToBigInt` agrees with the value denoted by a bitvector literal.
  def toBigIntPos: Boolean = { bitVectorToBigInt(5) == BigInt(5) }.holds
  def toBigIntNeg: Boolean = { bitVectorToBigInt(-1) == BigInt(-1) }.holds
  def toBigIntLong: Boolean = { bitVectorToBigInt(7L) == BigInt(7) }.holds

  // `bigIntToInt` / `bigIntToLong` agree with the bitvector for an in-range integer.
  def fromBigIntInt: Boolean = { bigIntToInt(BigInt(5)) == 5 }.holds
  def fromBigIntLong: Boolean = { bigIntToLong(BigInt(5)) == 7L - 2L }.holds

  // A 32-bit signed bitvector denotes a BigInt within the Int range.
  def intWithinRange(x: Int): Boolean = {
    bitVectorToBigInt(x) >= BigInt(-2147483648) && bitVectorToBigInt(x) <= BigInt(2147483647)
  }.holds

  // A 64-bit signed bitvector denotes a non-negative BigInt iff it is non-negative.
  def longSignAgrees(x: Long): Boolean = {
    (bitVectorToBigInt(x) >= 0) == (x >= 0L)
  }.holds
}
