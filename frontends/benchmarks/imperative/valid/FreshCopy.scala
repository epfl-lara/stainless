import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.annotation._

case class HasVar(var x: Int)

trait FreshCopy {
  var h: HasVar

  def f() = {
    require(h.x == 123)
    val freshH = freshCopy(h)
    h.x = 456
    assert(freshH.x == 123)
  }
}
