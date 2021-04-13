import stainless.math.BitVectors._

object UnsignedToSigned {
  def test = {
    val a: UInt3 = 4
    a.toSigned[Int3]
  }
}
