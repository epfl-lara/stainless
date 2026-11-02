import stainless.math.Unsigned._

object Unsigned2 {

  def test1(x: UInt): Unit = {
    assert(x.toInt.toUInt == x)
  }

  def test2(a: Array[Boolean], x: UByte): Unit = {
    require(a.length > 1 && a(1) && x == 1.toUByte)

    assert(a(x.toInt))
  }

  def test3: Unit = {
    val x: UByte = 255.toUByte
    assert(x.toByte == (-1: Byte))
  }

  def test4: Unit = {
    // Unsigned values are written with conversions from `Int`, `Long` or `BigInt` literals
    val x1: UByte = 145.toUByte
    val big: ULong = BigInt("18446744073709551615").toULong
    assert(big == ULong.MaxValue)

    val x2: Byte = x1.toByte // reinterpretation of the bits of an unsigned value as a signed value
    assert(x2 == (-111: Byte))

    // and conversely
    assert(x2.toUByte == x1)

    // Unsigned values can be converted to larger unsigned types (zero-extension)
    val x4: UShort = x1.toUShort
    assert(x4 == 145.toUShort)

    // or to smaller unsigned types (truncation).
    val x5: UByte = 401.toUShort.toUByte
    assert(x5 == 145.toUByte) // 401 % 2^8 == 145

    // Conversions to larger signed types preserve the value
    assert(x1.toInt == 145)

    // Signed values are sign-extended before being reinterpreted as unsigned values
    assert(x2.toUShort == 65425.toUShort) // 2^16 - 111

    // Constants for the minimum and maximum values
    assert(UByte.MaxValue == 255.toUByte)
    assert(UByte.MinValue == 0.toUByte)
  }

}
