import stainless.annotation.*
import stainless.io.*
import stainless.lang.*

/** Stainless verifies that matches are exhaustive, so GenC turns the last case
 *  of a match into the final `else` of the `if`/`else if` chain, without
 *  testing its pattern or its guard (issue #1806). The C compiler then sees
 *  that every path of a function returns a value, which GenCSuite checks with
 *  `-Werror=return-type`.
 */
object ExhaustiveMatch:

  // Only field-less leaves: GenC maps the hierarchy to a C enum
  sealed abstract class Color
  case class Red() extends Color
  case class Green() extends Color
  case class Blue() extends Color

  // Leaves with fields: GenC maps the hierarchy to a tagged union
  sealed abstract class Shape
  case class Square(side: Int) extends Shape
  case class Rect(width: Int, height: Int) extends Shape

  def code(c: Color): Int = c match
    case Red() => 0
    case Green() => 1
    case Blue() => 2

  def width(s: Shape): Int = s match
    case Square(side) => side
    case Rect(w, _) => w

  // Exhaustive thanks to the guards: the C code does not test the last one
  def sign(n: Int): Int = n match
    case m if m < 0 => -1
    case 0 => 0
    case m if m > 0 => 1

  // The match initialises a local variable: the C code assigns it in each branch
  def longestSide(s: Shape): Int =
    val side: Int = s match
      case Square(a) => a
      case Rect(w, h) => if w >= h then w else h
    if side < 0 then 0 else side

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState

    StdOut.println(code(Green())) // 1
    StdOut.println(code(Blue())) // 2
    StdOut.println(width(Square(3))) // 3
    StdOut.println(width(Rect(4, 5))) // 4
    StdOut.println(sign(-7)) // -1
    StdOut.println(sign(0)) // 0
    StdOut.println(sign(7)) // 1
    StdOut.println(longestSide(Rect(4, 5))) // 5
