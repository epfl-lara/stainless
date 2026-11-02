import stainless.math.Unsigned._

object NarrowUnsigned {
  def test = {
    val a: UShort = 300.toUShort
    a.toUByte
  }
}
