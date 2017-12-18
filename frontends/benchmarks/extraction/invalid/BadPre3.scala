import stainless.annotation._
import stainless.lang._

object BadPre3 {
  def reqfooreq(x: BigInt): BigInt = {
    require(x > 0)
    x + 1
    require(x < 0) // should be rejected
    assert(false)
    x
  }
}

