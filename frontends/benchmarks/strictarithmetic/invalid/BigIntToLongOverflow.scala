import stainless.lang._

object BigIntToLongOverflow {
  def tooBig: Long = bigIntToLong(BigInt("9223372036854775808"))
  def tooBig2: Long = bigIntToLong(BigInt("10000000000000000000000000000"))
}
