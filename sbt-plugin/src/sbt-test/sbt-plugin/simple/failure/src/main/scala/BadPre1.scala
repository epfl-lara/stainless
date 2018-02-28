import stainless.annotation._
import stainless.lang._

object BadPre1 {
  def reqreq(x: BigInt, y: BigInt): BigInt = {
    require(x > 0)
    require(y > 0) // should be rejected
    x + y
  } ensuring { _ > 0 }
}
