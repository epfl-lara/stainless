import stainless.lang._

object BigIntToLongUnderflow {
  def tooSmall: Long = BigInt("-9223372036854775809").toLong
  def tooSmall2: Long = BigInt("-10000000000000000000000000000").toLong
}
