import stainless.annotation.*
import stainless.io.*

/** `==` cannot compare values of unrelated classes in GenC. GenC represents
 *  both of these single-field classes by their field, so the C comparison would
 *  be `true` where Scala gives `false`.
 */
object EqualityOfUnrelatedSingleFieldClasses:

  case class A(x: Int)
  case class B(y: Int)

  def same(a: A, b: B): Boolean = a == b

  @cCode.`export`
  def main(): Unit =
    implicit val state: State = newState
    if same(A(1), B(1)) then StdOut.println("equal") else StdOut.println("different")
