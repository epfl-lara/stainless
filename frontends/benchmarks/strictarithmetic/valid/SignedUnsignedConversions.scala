import stainless.math.Unsigned._

object SignedUnsignedConversions {
  def test1 = {
    val a: UByte = 3.toUByte
    assert(a == a.toByte.toUByte)

    val b: UInt = 3.toUInt
    assert(b == b.toUByte.toUInt)

    // The value fits in a `UByte` (but not in a `Byte`)
    val c: Int = 200
    assert(c == c.toUByte.toInt)
  }

  def test2(x: UByte) = {
    assert(x == x.toInt.toUInt.toUByte)
  }

  def test3 = {
    val a = Array[Int](0, 100, 150, 132)
    val x0: UByte = 0.toUByte
    val x1: UByte = 1.toUByte
    val x2: UByte = 2.toUByte
    val x3: UByte = 3.toUByte
    assert(a(x0.toInt) == 0)
    assert(a(x1.toInt) == 100)
    assert(a(x2.toInt) == 150)
    assert(a(x3.toInt) == 132)

    val b = Array[Boolean](true, false, false, true)
    assert(b(x0.toInt))
    assert(!b(x1.toInt))
    assert(!b(x2.toInt))
    assert(b(x3.toInt))
  }
}
