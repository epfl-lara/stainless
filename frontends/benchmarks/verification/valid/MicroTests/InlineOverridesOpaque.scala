import stainless.annotation._
import stainless.lang.{inline => doInline}

object InlineOverridesOpaque {
  @opaque
  def f(): Int = 10

  def test(): Unit = {
    assert(doInline(f()) == 10)
  }
}
