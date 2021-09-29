import stainless.annotation._
import stainless.lang.unfold

object VisibleOpaque {
  @opaque def p(x: Int) = x > 0

  def test(x: Int): Unit = {
    unfold(p(x))
    assert(p(x) == x > 0)
  }
}
