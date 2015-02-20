import leon.annotation._
import leon.lang._

object FoolProofAdder {

  def foolProofAdder(x: BigInt): BigInt = {
    require(x > 0)
    x + BigInt(999999) + BigInt("999999999999999")
  } ensuring(_ > 0)

}
