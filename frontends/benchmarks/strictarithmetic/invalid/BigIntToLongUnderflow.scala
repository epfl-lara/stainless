import stainless.lang._

object BigIntToLongUnderflow {
  def tooSmall: Long = bigIntToLong(BigInt("-9223372036854775809"))
  def tooSmall2: Long = bigIntToLong(BigInt("-10000000000000000000000000000"))
}
