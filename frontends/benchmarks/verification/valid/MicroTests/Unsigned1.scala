import stainless.math.Unsigned._

object Unsigned1 {

  def test1(n1: UByte, n2: UByte, n3: UByte) = {
    require(n2 <= n3 && n1 <= n3 - n2 && n1 + n2 == n3)

    assert(n3 - n1 == n2)
  }

  def test2(n: UByte) = {
    assert((n ^ n) == 0.toUByte)
  }

  def test3(n: ULong) = {
    assert((n & n) == n)
    assert((n & 0.toULong) == 0.toULong)
  }

  def test4(n: ULong) = {
    assert((n | n) == n)
    assert((n | 0.toULong) == n)
  }

  def test5(n1: UInt, n2: UInt) = {
    require(n1 > n2)
    assert(n2 < n1)
  }

  def test6(n1: UInt, n2: UInt) = {
    require(n1 > n2)
    assert(n1 >= n2 + 1.toUInt)
  }

  def test7(n1: UByte, n2: UByte, n3: UByte) = {
    require(n2 != 0.toUByte && n1 <= n3 / n2 && n1 * n2 == n3)
    assert(n1 == n3 / n2)
  }

  def test8(n: ULong) = {
    assert((n % 2.toULong == 0.toULong) || (n % 2.toULong == 1.toULong))
  }

  def test9(n: ULong) = {
    assert(n >>> 1.toULong == n / 2.toULong)
  }

  def test10() = {
    assert(UByte.MinValue == 0.toUByte)
    assert(UByte.MaxValue == 255.toUByte)
    assert(ULong.MaxValue.toBigInt == BigInt("18446744073709551615"))
  }

  def test11(n: ULong) = {
    require(n <= ULong.MaxValue / 2.toULong)
    assert(n << 1.toULong == n * 2.toULong)
  }

  def test12(n: UShort) = {
    require(n == 42.toUShort)
    val m = n.toUInt
    assert(m == 42.toUInt)
  }

  def test13(n: UShort) = {
    require(n == 300.toUShort)
    val m = n.toUByte
    assert(m == 44.toUByte)
  }

  def test14() = {
    val zero: UInt = 0.toUInt
    assert(~zero == UInt.MaxValue)
    assert(-1.toUInt == UInt.MaxValue)
  }

  def test15(n: UInt) = {
    assert(~(~n) == n)
  }

  // Shifting by the size of the type or more gives 0
  def test16(n: UByte, k: UByte) = {
    require(k >= 8.toUByte)
    assert(n << k == 0.toUByte)
    assert(n >>> k == 0.toUByte)
  }

  def test17(n: UInt) = {
    assert(n.toBigInt >= 0 && n.toBigInt <= BigInt(4294967295L))
    assert(n.toULong.toBigInt == n.toBigInt)
  }

  // `toStringUnsigned` is an uninterpreted function for Stainless: it only depends on its argument
  def test18(x: ULong, y: ULong) = {
    require(x == y)
    assert(x.toStringUnsigned == y.toStringUnsigned)
  }

}
