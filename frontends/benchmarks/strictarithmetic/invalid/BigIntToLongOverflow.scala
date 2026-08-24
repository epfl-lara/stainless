import stainless.lang._

object BigIntToLongOverflow {
  // 2^63 is one past Long.MaxValue: `.toLong` would wrap around, so under strict
  // arithmetic the conversion is rejected.
  def tooBig: Long = BigInt("9223372036854775808").toLong
  def tooBig2: Long = BigInt("10000000000000000000000000000").toLong
}
