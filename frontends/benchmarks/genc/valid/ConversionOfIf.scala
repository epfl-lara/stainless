import stainless.annotation.*
import stainless.io.*
import stainless.lang.*
import stainless.math.Unsigned.*

/** An integer conversion applied to an `if`, a `match`, or an expression that
 *  contains one: GenC declares a variable, assigns it in each branch, and
 *  converts the variable, as it does for the operand of any other operator
 *  (issue #1918). Before, the statements of the branches were printed inside
 *  the operand of the C cast.
 */
object ConversionOfIf:

  @extern
  @cCode.function(
    code = """
      |void __FUNCTION__(int64_t x) {
      |  printf("%"PRIi64"\n", x);
      |}
      """,
    headerIncludes = "inttypes.h:stdio.h",
    cIncludes = ""
  )
  def printlnLong(x: Long)(implicit @ghost state: State): Unit =
    scala.Predef.println(x)

  def widen(c: Boolean, a: Int, b: Int): Long =
    (if c then a else b).toLong

  def widenOr(c: Boolean, a: Int): Long =
    (a | (if c then 1 else 0)).toLong

  def narrow(c: Boolean, a: Int, b: Int): Byte =
    require(-128 <= a && a <= 127 && -128 <= b && b <= 127)
    (if c then a else b).toByte

  def toUnsigned(c: Boolean, a: Int, b: Int): UByte =
    require(0 <= a && a <= 255 && 0 <= b && b <= 255)
    (if c then a else b).toUByte

  def ofMatch(n: Int): Long =
    (n match
      case 0 => 10
      case _ => 20
    ).toLong

  def twice(x: Long): Long =
    require(-1000L <= x && x <= 1000L)
    2L * x

  // The converted value is the argument of a call
  def inArgument(c: Boolean, a: Int, b: Int): Long =
    require(-500 <= a && a <= 500 && -500 <= b && b <= 500)
    twice((if c then a else b).toLong)

  // The converted value is computed again before each iteration
  def inCondition(c: Boolean, n: Int): Int =
    require(0 <= n && n <= 100)
    var i: Int = 0
    (while ((if c then i else i + 1).toLong < n.toLong) {
      decreases(n - i)
      i = i + 1
    }).invariant(0 <= i && i <= n)
    i

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState

    printlnLong(widen(true, 1, 2)) // 1
    printlnLong(widen(false, 1, 2)) // 2
    printlnLong(widenOr(true, 4)) // 5
    printlnLong(widenOr(false, 4)) // 4
    printlnLong(narrow(true, -3, 100).toLong) // -3
    printlnLong(narrow(false, -3, 100).toLong) // 100
    StdOut.printlnU8(toUnsigned(true, 200, 7)) // 200
    StdOut.printlnU8(toUnsigned(false, 200, 7)) // 7
    printlnLong(ofMatch(0)) // 10
    printlnLong(ofMatch(3)) // 20
    printlnLong(inArgument(false, 1, 21)) // 42
    StdOut.println(inCondition(true, 3)) // 3
    StdOut.println(inCondition(false, 3)) // 2
