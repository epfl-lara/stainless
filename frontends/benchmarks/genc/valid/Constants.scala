import stainless.annotation._
import stainless.lang._
import stainless.math.BitVectors._
import stainless.io._

// Top-level `val`s are immutable, so GenC emits them as `static const` globals (defined in the
// header when exported, or as `#define` macros with `@cCode.define`), including constants of
// class types.
object Constants {

  case class Point(x: Int, y: Int)
  case class Rect(topLeft: Point, bottomRight: Point)

  sealed abstract class Shape
  case class Circle(radius: Int) extends Shape
  case class Square(side: Int) extends Shape

  sealed abstract class Color
  case class Red() extends Color
  case class Green() extends Color

  object Limits {
    val MaxF: Int = 65535
    val ErrMalformed: Int = -2
  }

  // Primitive constants of various types
  val Flag: Boolean = true
  val Small: Byte = -8
  val Medium: Short = 1234
  val Big: Long = 123456789012L
  val Letter: Char = 'z'
  val Unsigned: UInt32 = BigInt("4000000000")

  // Constants defined in terms of other constants: their values are inlined in C,
  // as `const` variables are not constant expressions there.
  val MaxPlusOne: Int = Limits.MaxF + 1
  val Twice: Int = MaxPlusOne * 2

  // Constants of class types
  val Origin: Point = Point(0, 0)
  val UnitSquare: Rect = Rect(Origin, Point(1, 1))
  val DefaultShape: Shape = Circle(5)
  val DefaultColor: Color = Green()

  // Exported constants are defined in the header file, even when not used by the Scala code
  @cCode.`export`
  val Version: Int = 3

  @cCode.`export`
  val Center: Point = Point(50, 50)

  // Constants translated to preprocessor macros
  @cCode.define
  val BufferSize: Int = 16

  // Macros are referred to by name from the initial values of constants defined in the C file,
  // and inlined in the initial values of constants defined in the header (unless exported too)
  val DoubleBuffer: Int = BufferSize * 2

  @cCode.`export`
  val Limit: Int = BufferSize + 1

  // Function constants (lambdas directly calling a named function) become constant function pointers;
  // exported ones must refer to exported functions, as they are defined in the header
  val Inc: Int => Int = (x: Int) => incImpl(x)

  @cCode.`export`
  val Op: Int => Int = (x: Int) => check(x)

  // Lazy vals are translated like vals
  lazy val Lazy: Int = 7

  // Constants that are neither used nor exported are not emitted
  val Unused: Int = 42

  @cCode.`export`
  def check(f: Int): Int = {
    if (0 < f && f <= Limits.MaxF) f else Limits.ErrMalformed
  }

  def area(s: Shape): Int = s match {
    case Circle(r) => 3 * r * r
    case Square(side) => side * side
  }

  def isGreen(c: Color): Boolean = c match {
    case Green() => true
    case Red() => false
  }

  def width(r: Rect): Int = r.bottomRight.x - r.topLeft.x

  def incImpl(x: Int): Int = x + 1

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState
    StdOut.println(check(100))
    StdOut.println(check(70000))
    StdOut.println(MaxPlusOne)
    StdOut.println(Twice)
    StdOut.println(if (Flag) 1 else 0)
    StdOut.println(Small.toInt)
    StdOut.println(Medium.toInt)
    StdOut.println((Big % 1000).toInt)
    StdOut.println(Letter)
    StdOut.printlnU32(Unsigned)
    StdOut.println(Origin.x + UnitSquare.bottomRight.y)
    StdOut.println(area(DefaultShape))
    StdOut.println(if (isGreen(DefaultColor)) 1 else 0)
    StdOut.println(width(UnitSquare))
    StdOut.println(BufferSize)
    StdOut.println(Inc(41))
    StdOut.println(Op(5))
    StdOut.println(Lazy)
    StdOut.println(DoubleBuffer)
    StdOut.println(Limit)
  }
}
