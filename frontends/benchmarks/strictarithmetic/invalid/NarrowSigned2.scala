import stainless.math.BitVectors._

object NarrowSigned2 {
  def test = {
    val a: Int4 = -5
    a.narrow[Int3]
  }
}
