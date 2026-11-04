import stainless.math.Unsigned._

object Unsigned3 {

  // As for `Int` (see Unsigned2), comparing with a `BigInt` would compare it with the signed representation of `v`
  def test(v: UByte) = {
    v == BigInt(200)
  }

}
