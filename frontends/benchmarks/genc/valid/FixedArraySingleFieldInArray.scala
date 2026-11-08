import stainless.annotation.*

/** An array of instances of a class whose single field is an array of a length
 *  fixed by its invariant, in a field of another class. GenC used to crash on
 *  it (#1283).
 */
object FixedArraySingleFieldInArray:

  @inline @cCode.inline
  val DictionarySize: Int = 6

  @inline @cCode.inline
  val BufferSize: Int = 4

  case class Dictionary(buffers: Array[Buffer], var nextIndex: Int)

  case class Buffer(array: Array[Byte]):
    require(array.length == BufferSize)

  @cCode.`export`
  def main(): Int =
    val dictionary: Dictionary =
      Dictionary(Array.fill(DictionarySize)(Buffer(Array.fill(BufferSize)(0))), 0)
    0
