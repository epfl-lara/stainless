import stainless.math.BitVectors._

object BitVectors3 {

  def test(v: UInt5) = {
    v.widen[UInt4]
  }

}
