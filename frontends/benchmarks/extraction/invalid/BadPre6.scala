import stainless.annotation._
import stainless.lang._

object BadPre6 {
  def outer(x: BigInt): BigInt = {

    def inner(y: BigInt): BigInt = {
      require(x > y)
      require(x > y) // should be rejected
      y
    }

    inner(x / 2)
  }
}

