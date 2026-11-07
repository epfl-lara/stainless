import stainless.annotation.*
import stainless.io.*

/** A class whose single field is an array of a length fixed by its invariant.
 *  GenC replaces the other classes with a single field by their field, but
 *  keeps this one as a C struct, which the array is a part of.
 */
object FixedArraySingleField:

  @cCode.`export`
  case class Buffer(data: Array[Int]):
    require(data.length == 4)

  case class Packet(payload: Buffer, id: Int)

  @cCode.`export`
  def get(b: Buffer, i: Int): Int =
    require(0 <= i && i < 4)
    b.data(i)

  def set(b: Buffer, i: Int, v: Int): Unit =
    require(0 <= i && i < 4)
    b.data(i) = v

  def printBuffers()(implicit @ghost state: State): Unit =
    // A local value, passed to functions
    val b: Buffer = Buffer(Array(1, 2, 3, 4))
    set(b, 2, 9)
    StdOut.println(get(b, 2)) // 9
    StdOut.println(get(b, 3)) // 4

    // A value that only contains zeroes
    val z: Buffer = Buffer(Array.fill(4)(0))
    z.data(1) = 5
    StdOut.println(get(z, 0)) // 0
    StdOut.println(get(z, 1)) // 5

    // A value nested in another value
    val p: Packet = Packet(Buffer(Array.fill(4)(7)), 6)
    p.payload.data(1) = 3
    StdOut.println(p.payload.data(1)) // 3
    StdOut.println(get(p.payload, 0)) // 7
    StdOut.println(p.id) // 6

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState
    printBuffers()
