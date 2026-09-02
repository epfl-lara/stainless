import stainless.lang._

object BigIntToIntUnderflow {
  // One below Int.MinValue: `.toInt` would wrap around, so under strict
  // arithmetic the conversion is rejected.
  def tooSmall: Int = BigInt("-2147483649").toInt
  def tooSmall2: Int = BigInt("-10000000000000").toInt
}
