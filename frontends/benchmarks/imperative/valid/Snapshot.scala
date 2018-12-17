import stainless.lang._
import stainless.annotation._
import stainless.lang.StaticChecks._

trait Test {
  var x: BigInt

  def f() = {
    require(x == 0)
    @ghost val old = snapshot(this)
    x = 1
    assert(old.x == 0)
  }
}
