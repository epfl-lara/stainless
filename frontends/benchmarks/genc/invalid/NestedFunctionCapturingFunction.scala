import stainless.annotation.*

/** GenC does not support nested functions that capture a function, as it passes
 *  captured variables by reference.
 */
object NestedFunctionCapturingFunction:

  def inc(x: Int): Int = x + 1

  def outer(f: Int => Int, y: Int): Int =
    def g(z: Int): Int = f(z)
    g(y)

  @cCode.`export`
  def main(): Unit =
    val r: Int = outer((x: Int) => inc(x), 1)
    ()
