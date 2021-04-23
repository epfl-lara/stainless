import stainless.math.BitVectors._

object SignedToUnsigned {
  def test = {
    val a: Int3 = -1
    a.toUnsigned[UInt3]
  }
}
