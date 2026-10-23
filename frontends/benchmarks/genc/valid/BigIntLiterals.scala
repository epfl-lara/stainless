import stainless.annotation._
import stainless.lang._
import stainless.math.BitVectors._
import stainless.io._

// `BigInt` literals converted to bitvectors (`bigIntToBV`) become C literals.
object BigIntLiterals {

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState
    val a: UInt8 = BigInt(200)
    val b: UInt16 = BigInt(60000)
    val c: UInt32 = BigInt("4000000000")
    val d: UInt64 = BigInt("5000000000")
    StdOut.printlnU8(a)
    StdOut.printlnU16(b)
    StdOut.printlnU32(c)
    StdOut.printlnU64(d)
    val e: Int8 = BigInt(-100)
    val f: Int16 = BigInt(-30000)
    val g: Int32 = BigInt(-2000000000)
    val h: Int64 = BigInt("-5000000000")
    assert(h < (0: Int64))
    StdOut.println(e.toInt)
    StdOut.println(f.toInt)
    StdOut.println(g.toInt)
  }

}
