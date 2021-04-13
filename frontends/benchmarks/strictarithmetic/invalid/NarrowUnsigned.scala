import stainless.math.BitVectors._

object NarrowUnsigned {
  def test = {
    val a: UInt3 = 5
    a.narrow[UInt2]
  }
}
