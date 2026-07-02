import stainless.lang._

object BigIntToBVInRange {

  // Literals within range: the conversion cannot lose information.
  def smallInt: Int = BigInt(5).toInt
  def smallLong: Long = BigInt(5).toLong

  // The Int bounds themselves are representable.
  def maxInt: Int = BigInt(2147483647).toInt
  def minInt: Int = BigInt(-2147483648).toInt

  // Guarded by a precondition pinning the value to the Int range.
  def guardedInt(i: BigInt): Int = {
    require(i >= BigInt(-2147483648) && i <= BigInt(2147483647))
    i.toInt
  }

  // Guarded by a precondition pinning the value to the Long range.
  def guardedLong(i: BigInt): Long = {
    require(i >= BigInt("-9223372036854775808") && i <= BigInt("9223372036854775807"))
    i.toLong
  }
}
