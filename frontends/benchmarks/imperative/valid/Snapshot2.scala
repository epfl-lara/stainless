import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.annotation.{ghost => ghostAnnot}

trait Snapshot2 {
  var x: BigInt

  def f() = {
    require(x == 2)
    @ghostAnnot val other = snapshot(this)
    ghost { other.x = 5 }
    assert(x == 2)
    assert(other.x == 5)
  }
}
