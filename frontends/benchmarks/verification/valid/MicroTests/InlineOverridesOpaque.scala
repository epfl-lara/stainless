import stainless.annotation._
import stainless.lang.inline

object InlineOverridesOpaque {
  @opaque
  def f(): Int = 10

  def test(): Unit = {
    assert(inline(f()) == 10)
  }
}
