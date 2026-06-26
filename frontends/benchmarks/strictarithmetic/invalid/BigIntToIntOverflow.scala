import stainless.lang._

object BigIntToIntOverflow {
  // 2^31 is one past Int.MaxValue: `.toInt` would wrap around, so under strict
  // arithmetic the conversion is rejected.
  def tooBig: Int = BigInt("2147483648").toInt
  def tooBig2: Int = BigInt("10000000000000").toInt
}
