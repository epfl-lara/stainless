import stainless.math.Unsigned._

object SignedToUnsigned {
  def test = {
    val a: Int = -1
    a.toUInt
  }
}
