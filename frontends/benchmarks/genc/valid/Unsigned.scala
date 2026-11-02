import stainless.annotation._
import stainless.lang._
import stainless.math.Unsigned._
import stainless.io._

object Unsigned {

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState
    val a = fa(16.toULong, 84.toULong)
    val b = fb(84.toUInt, 14.toUInt)
    val c = fc(5.toUShort, 7.toUShort)
    val d = fd(126.toUByte, 3.toUByte)
    assert(a == 100.toULong)
    assert(b == 70.toUInt)
    assert(c == 35.toUShort)
    assert(d == 42.toUByte)
    StdOut.printlnU64(a)
    StdOut.printlnU32(b)
    StdOut.printlnU16(c)
    StdOut.printlnU8(d)
  }

  def fa(x: ULong, y: ULong) = {
    require(x < 200.toULong && y < 200.toULong)
    x + y
  }

  def fb(x: UInt, y: UInt) = {
    require(y <= x && x < 200.toUInt)
    x - y
  }

  def fc(x: UShort, y: UShort) = {
    require(x < 200.toUShort && y < 200.toUShort)
    x * y
  }

  def fd(x: UByte, y: UByte) = {
    require(x < 200.toUByte && y > 0.toUByte && y < 200.toUByte)
    x / y
  }

}
