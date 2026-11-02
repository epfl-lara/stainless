import stainless.math.Unsigned._

object Unsigned2 {

  // On the JVM, `v == 200` compares 200 with the signed representation of `v` (-56 when `v` is 200)
  def test(v: UByte) = {
    v == 200
  }

}
