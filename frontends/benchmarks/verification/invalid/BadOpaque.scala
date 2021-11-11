import stainless.annotation._

object BadOpaque {
  @opaque
  def test(): Unit = {
    assert(false)
    ()
  }
}
