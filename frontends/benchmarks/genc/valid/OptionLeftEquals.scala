import stainless.annotation.*
import stainless.io.*
import stainless.lang.*

/** `==` and `!=` with an instance of a subclass of `Option` on the left,
 *  compared with an `Option` or with an instance of the other subclass. GenC
 *  compares them with the equality function of `Option`.
 */
object OptionLeftEquals:

  def isNone(o: Option[Int]): Boolean = None[Int]() == o

  def differsFromOne(o: Option[Int]): Boolean = Some(1) != o

  def printAnswer(b: Boolean)(implicit @ghost state: State): Unit =
    if b then StdOut.println("yes") else StdOut.println("no")

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState
    printAnswer(isNone(Some(1))) // no
    printAnswer(isNone(None())) // yes
    printAnswer(differsFromOne(Some(1))) // no
    printAnswer(differsFromOne(Some(2))) // yes
    printAnswer(differsFromOne(None())) // yes
    printAnswer(Some(1) == None[Int]()) // no
