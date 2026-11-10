import stainless.annotation.*

/** GenC does not support arrays of functions, including arrays of a class with
 *  a single field of function type, which GenC represents by its field.
 */
object ArrayOfFunctionWrappers:

  case class F(f: Int => Int)

  def inc(x: Int): Int = x + 1

  @cCode.`export`
  def main(): Unit =
    val fs: Array[F] = Array[F](F((x: Int) => inc(x)))
    val r: Int = fs(0).f(1)
    ()
