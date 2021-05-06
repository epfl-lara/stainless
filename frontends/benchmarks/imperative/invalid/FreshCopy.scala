import stainless.lang._

case class HasVar(var x: Int)

trait FreshCopy {
  var h: HasVar

  def f() = {
    require(h.x == 123)
    val freshH = h // call to freshCopy is missing
    h.x = 456
    assert(freshH.x == 123)
  }
}
