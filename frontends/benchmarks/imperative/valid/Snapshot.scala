import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.annotation._

trait Snapshot {
  var x: BigInt

  def f() = {
    require(x == 0)
    @ghost val old = snapshot(this)
    x = 1
    assert(old.x == 0)
  }
}
