import stainless.annotation._
import stainless.lang._

object BadPre7 {

  case class C(x: BigInt) {
    def method: BigInt = {
      require(x > 0)
      require(x > 0) // should be rejected
      x
    }
  }
}

