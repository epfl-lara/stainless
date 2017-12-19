import stainless.annotation._
import stainless.lang._

object BadPre5 {
  def lambda(x: BigInt): BigInt = {

    val f: BigInt => BigInt = { y =>
      require(x > y)
      require(x > y) // should be rejected
      y
    }

    f(x / 2)
  }
}

