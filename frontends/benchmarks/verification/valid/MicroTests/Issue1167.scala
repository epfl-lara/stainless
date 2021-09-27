import stainless.annotation._

object Issue1167 {
  @opaque @inlineOnce def f(x: Int): Int = 0
  def test = assert(f(10) == f(10))
}
