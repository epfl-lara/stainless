import stainless.annotation.*

/** GenC does not support values of function types that take or return
 *  functions.
 */
object HigherOrderFunctionValue:

  def inc(x: Int): Int = x + 1

  def applyIt(g: Int => Int, x: Int): Int = g(x)

  @cCode.`export`
  def main(): Unit =
    val h: (Int => Int, Int) => Int = (g: Int => Int, x: Int) => applyIt(g, x)
    val r: Int = h((x: Int) => inc(x), 1)
    ()
