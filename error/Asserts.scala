import leon.annotation._
import leon.lang._
import leon.lang._

object Asserts {

  def assert1(i: BigInt): BigInt = { // we might define assert like so
    require(i >= 0)
    i
  }

  def sum(to: BigInt): BigInt = {
    assert1(to)
    to
  }
}
