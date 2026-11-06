import stainless.annotation.*

/** GenC does not evaluate the size of the array given to a field of a length
 *  fixed by a class invariant, as the array gets that length: it rejects a
 *  size with effects.
 */
object FixedArraySizeWithEffects:

  case class Counter(var n: Int)

  case class Buffer(data: Array[Int], size: Int):
    require(data.length == 3)

  def three(c: Counter): Int = {
    require(0 <= c.n && c.n < 1000)
    c.n += 1
    3
  }.ensuring(_ == 3)

  @cCode.`export`
  def f(): Int =
    val c: Counter = Counter(0)
    val b: Buffer = Buffer(Array.fill(three(c))(0), 0)
    b.data(1) + c.n
