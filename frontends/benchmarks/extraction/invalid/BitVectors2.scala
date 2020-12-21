import stainless.math.BitVectors._

object BitVectors2 {

  def test(v: UInt5) = {
    v.widen[Int5]
  }

}
