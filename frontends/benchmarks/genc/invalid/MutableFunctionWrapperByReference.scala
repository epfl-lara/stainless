import stainless.annotation.*

/** GenC does not support references to a mutable class with a single field of
 *  function type, as it represents the class by its field.
 */
object MutableFunctionWrapperByReference:

  case class Box(var f: Int => Int)

  def inc(x: Int): Int = x + 1

  def dec(x: Int): Int = x - 1

  def setDec(b: Box): Unit =
    b.f = (x: Int) => dec(x)

  @cCode.`export`
  def main(): Unit =
    val b: Box = Box((x: Int) => inc(x))
    setDec(b)
    val r: Int = b.f(1)
    ()
