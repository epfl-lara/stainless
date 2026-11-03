import stainless.annotation._

// The length of a fixed-length array field must be positive, as C forbids zero-length arrays, but
// only the classes compiled to C are checked: `W` and `length` are not used by the exported code.
object FixedArrayEmptyUnused {

  case class W(x: Int, a: Array[Int]) {
    require(a.length == 0)
  }

  def length(w: W): Int = w.x + w.a.length

  @cCode.`export`
  def main(): Int = 0

}
