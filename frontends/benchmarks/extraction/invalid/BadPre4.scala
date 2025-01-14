import stainless.annotation._
import stainless.lang._

object BadPre4 {
  def decreq(x: BigInt): BigInt = {
    decreases(x)
    decreases(x + 1) // should be rejected
    if (x == 0) BigInt(0) else decreq(x - x)
 }.ensuring { _ == 0 }
}

