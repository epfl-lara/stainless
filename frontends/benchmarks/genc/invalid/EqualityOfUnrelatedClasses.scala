import stainless.annotation.*

/** `==` cannot compare values of unrelated classes in GenC: the C equality
 *  function of `A` cannot take a `B`.
 */
object EqualityOfUnrelatedClasses:

  case class A(x: Int, y: Int)
  case class B(x: Int, y: Int)

  def same(a: A, b: B): Boolean = a == b

  @cCode.`export`
  def main(): Unit =
    val r: Boolean = same(A(1, 2), B(1, 2))
    ()
