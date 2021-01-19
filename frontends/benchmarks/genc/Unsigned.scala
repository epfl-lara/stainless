import stainless.annotation._
import stainless.lang._
import stainless.math.BitVectors._
import stainless.io._

object Unsigned {

  @extern
  def main(args: Array[String]): Unit = _main()

  def _main(): Int = {
    val a = fa(16, 84)
    val b = fb(84, 14)
    val c = fc(5, 7)
    val d = fd(126, 3)
    assert(a == 100)
    assert(b == 70)
    assert(c == 35)
    assert(d == 42)
    StdOut.printlnU64(a)
    StdOut.printlnU32(b)
    StdOut.printlnU16(c)
    StdOut.printlnU8(d)
    0
  }

  def fa(x: UInt64, y: UInt64) = {
    x + y
  }

  def fb(x: UInt32, y: UInt32) = {
    x - y
  }

  def fc(x: UInt16, y: UInt16) = {
    x * y
  }

  def fd(x: UInt8, y: UInt8) = {
    x / y
  }

}
