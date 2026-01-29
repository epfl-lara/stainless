import stainless.annotation._
import stainless.lang.unfolding

object VisibleOpaque {
  @opaque def p(x: Int) = x > 0

  def test(x: Int): Unit = {
    unfolding(p(x))
    assert(p(x) == x > 0)
  }
}
