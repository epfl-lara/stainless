import stainless.lang.*

object IntToBigInt:
  // The implicit conversion keeps the sign
  def implicitIsNonNegative(x: Int): Boolean = {
    val b: BigInt = x
    b >= 0
  }.holds

  def implicitLongIsInIntRange(x: Long): Boolean = {
    val b: BigInt = x
    b <= BigInt(2147483647)
  }.holds

  // Both branches of the `if` are converted
  def ifArgumentIsOne(c: Boolean): Boolean = {
    BigInt(if c then 1 else 0) == 1
  }.holds
