import stainless.lang._

object BitVectorBigIntConversions {

  // `BigInt(x)` on a machine integer gives the mathematical integer it represents:
  // a 32-bit signed value lies within the Int range.
  def intWithinRange(x: Int): Boolean = {
    BigInt(x) >= BigInt(-2147483648) && BigInt(x) <= BigInt(2147483647)
  }.holds

  // Sign is preserved by the conversion to BigInt.
  def intSignAgrees(x: Int): Boolean = {
    (BigInt(x) >= 0) == (x >= 0)
  }.holds

  def longSignAgrees(x: Long): Boolean = {
    (BigInt(x) >= 0) == (x >= 0L)
  }.holds

  // `BigInt(_).toInt` / `.toLong` round-trip an in-range value.
  def fromBigIntInt: Boolean = { BigInt(5).toInt == 5 }.holds
  def fromBigIntLong: Boolean = { BigInt(5).toLong == 5L }.holds
}
