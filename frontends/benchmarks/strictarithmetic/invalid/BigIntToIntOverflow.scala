import stainless.lang._

object BigIntToIntOverflow {
  def tooBig: Int = bigIntToInt(BigInt("2147483648"))
  def tooBig2: Int = bigIntToInt(BigInt("10000000000000"))
}
