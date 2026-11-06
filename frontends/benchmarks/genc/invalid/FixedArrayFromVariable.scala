import stainless.annotation.*

/** An array field of a length fixed by a class invariant is part of the C
 *  struct of its class, so it cannot refer to another array: GenC only accepts
 *  an array literal or `Array.fill` for it.
 */
object FixedArrayFromVariable:

  case class Buffer(data: Array[Int], size: Int):
    require(data.length == 3)

  @cCode.`export`
  def f(): Int =
    val a: Array[Int] = Array(1, 2, 3)
    val b: Buffer = Buffer(a, 0)
    b.data(1)
