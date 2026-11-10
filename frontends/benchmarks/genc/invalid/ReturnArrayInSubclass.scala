import stainless.annotation.*

/** The array is in a subclass of the returned class, so the C function would
 *  return a pointer to its local array.
 */
object ReturnArrayInSubclass:

  sealed trait OptionArray

  case class SomeArray(arr: Array[Int]) extends OptionArray

  case class NoneArray() extends OptionArray

  def test(): OptionArray =
    SomeArray(Array.fill(10)(1))

  @cCode.`export`
  def main(): Int =
    val oa: OptionArray = test()
    0
