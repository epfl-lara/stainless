import stainless.math.BitVectors._

object NarrowSigned1 {
  def test = {
    val a: Int4 = 5
    a.narrow[Int3]
  }
}
