import stainless.annotation._

object Issue1167b {
  @opaque @inlineOnce def f(x: Int): Int = 0
  def test = assert(f(0) == f(1))
}
