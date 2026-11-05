import stainless.annotation.*

/** GenC does not support variable-length arrays whose elements contain arrays,
 *  even when they only contain zeroes: zero-filling the array would make it
 *  empty.
 */
object VariableLengthArrayOfArrays:

  case class Inner(a: Array[Int])

  @cCode.`export`
  def f(n: Int): Int =
    require(0 < n && n <= 10)
    val arr: Array[Inner] = Array.fill(n)(Inner(Array.fill(2)(0)))
    arr.length
