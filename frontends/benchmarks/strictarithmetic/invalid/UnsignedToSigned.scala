import stainless.math.Unsigned._

object UnsignedToSigned {
  def test = {
    val a: UByte = 200.toUByte
    a.toByte
  }
}
