import stainless.lang._

object BigIntToIntUnderflow {
  def tooSmall: Int = bigIntToInt(BigInt("-2147483649"))
  def tooSmall2: Int = bigIntToInt(BigInt("-10000000000000"))
}
