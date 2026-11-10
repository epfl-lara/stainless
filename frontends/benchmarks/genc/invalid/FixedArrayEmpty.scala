import stainless.annotation._

// The length of a fixed-length array field must be positive: C forbids zero-length arrays.
object FixedArrayEmpty {

  case class W(x: Int, a: Array[Int]) {
    require(a.length == 0)
  }

  @cCode.`export`
  def f(w: W): Int = w.x + w.a.length

}
