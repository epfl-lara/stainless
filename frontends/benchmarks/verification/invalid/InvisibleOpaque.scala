import stainless.annotation._

object InvisibleOpaque {
  @opaque def p(x: Int) = x > 0

  def test(x: Int): Unit = {
    assert(p(x) == x > 0)
  }
}
