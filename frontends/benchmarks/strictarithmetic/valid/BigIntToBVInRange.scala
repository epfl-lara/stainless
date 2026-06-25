import stainless.lang._

object BigIntToBVInRange {

  // Literals within range: the conversion cannot lose information.
  def smallInt: Int = bigIntToInt(BigInt(5))
  def smallLong: Long = bigIntToLong(BigInt(5))

  // The Int bounds themselves are representable.
  def maxInt: Int = bigIntToInt(BigInt(2147483647))
  def minInt: Int = bigIntToInt(BigInt(-2147483648))

  // Guarded by a precondition pinning the value to the Int range.
  def guardedInt(i: BigInt): Int = {
    require(i >= BigInt(-2147483648) && i <= BigInt(2147483647))
    bigIntToInt(i)
  }

  // Guarded by a precondition pinning the value to the Long range.
  def guardedLong(i: BigInt): Long = {
    require(i >= BigInt("-9223372036854775808") && i <= BigInt("9223372036854775807"))
    bigIntToLong(i)
  }
}
