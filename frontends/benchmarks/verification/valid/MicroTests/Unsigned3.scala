import stainless.math.Unsigned._

// `BigInt` literals converted to unsigned integers, in range.
object Unsigned3 {

  def test1 = {
    val a: UByte = BigInt(200).toUByte
    assert(a > 100.toUByte)
  }

  def test2 = {
    val min: UByte = BigInt(0).toUByte
    val max: UByte = BigInt(255).toUByte
    assert(min < max)
  }

  def test3 = {
    val a: UInt = BigInt("4000000000").toUInt
    assert(a == 4000000000L.toUInt)
  }

  def test4 = {
    val a: ULong = BigInt("18446744073709551615").toULong // 2^64 - 1
    assert(a == ULong.MaxValue)
  }

}
