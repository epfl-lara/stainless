import stainless.annotation._
import stainless.lang._
import stainless.math.Unsigned._
import stainless.io._

// `BigInt` literals converted to unsigned integers become C literals.
object BigIntLiterals {

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState
    val a: UByte = BigInt(200).toUByte
    val b: UShort = BigInt(60000).toUShort
    val c: UInt = BigInt("4000000000").toUInt
    val d: ULong = BigInt("5000000000").toULong
    val e: ULong = BigInt("18446744073709551615").toULong
    StdOut.printlnU8(a)
    StdOut.printlnU16(b)
    StdOut.printlnU32(c)
    StdOut.printlnU64(d)
    StdOut.printlnU64(e)
  }

}
