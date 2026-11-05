import stainless.annotation.*
import stainless.io.*

/** `==` and `!=` with an instance of a subclass on the left, compared with a
 *  value of the class hierarchy or with an instance of the same or of another
 *  subclass. GenC compares them with the equality function of the top class of
 *  the hierarchy, which represents all its classes in C.
 */
object ChildLeftEquals:

  sealed abstract class Shape
  case class Circle(r: Int) extends Shape
  case class Square(s: Int) extends Shape

  def isUnitCircle(s: Shape): Boolean = Circle(1) == s

  def isNotUnitSquare(s: Shape): Boolean = Square(1) != s

  def printAnswer(b: Boolean)(implicit @ghost state: State): Unit =
    if b then StdOut.println("yes") else StdOut.println("no")

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState
    printAnswer(isUnitCircle(Square(1))) // no
    printAnswer(isUnitCircle(Circle(1))) // yes
    printAnswer(isUnitCircle(Circle(2))) // no
    printAnswer(isNotUnitSquare(Square(1))) // no
    printAnswer(isNotUnitSquare(Circle(1))) // yes
    printAnswer(Circle(1) == Square(1)) // no
    printAnswer(Circle(1) == Circle(1)) // yes
    printAnswer(Square(2) != Circle(2)) // yes
