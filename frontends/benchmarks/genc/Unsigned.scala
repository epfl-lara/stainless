import stainless.annotation._
import stainless.lang._
import stainless.math.BitVectors._
import stainless.io._

object Unsigned {

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState
    val a = fa(16, 84)
    val b = fb(84, 14)
    val c = fc(5, 7)
    val d = fd(126, 3)
    assert(a == (100: UInt64))
    assert(b == (70: UInt32))
    assert(c == (35: UInt16))
    assert(d == (42: UInt8))
    StdOut.printlnU64(a)
    StdOut.printlnU32(b)
    StdOut.printlnU16(c)
    StdOut.printlnU8(d)
  }

  def fa(x: UInt64, y: UInt64) = {
    require(0 <= x && x < 200 && 0 <= y && y < 200)
    x + y
  }

  def fb(x: UInt32, y: UInt32) = {
    require(0 <= y && y <= x && x < 200)
    x - y
  }

  def fc(x: UInt16, y: UInt16) = {
    require(0 <= x && x < 200 && 0 <= y && y < 200)
    x * y
  }

  def fd(x: UInt8, y: UInt8) = {
    require(0 <= x && x < 200 && 0 < y && y < 200)
    x / y
  }

}
