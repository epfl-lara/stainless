import stainless.annotation._

object Issue1167 {
  @opaque @inlineOnce def f: Int = 0
  @opaque @inlineOnce def g: Int = 1
  def test = assert(f == g)
}
