import stainless.lang._
import stainless.annotation._

object PrecondWitness5 {
  // @extern functions can have witnesses too: only their specification is used
  @extern
  def sqrt(x: BigInt): BigInt = {
    require(x >= 0)
    precondWitness(sqrt(16))
    x // The body of an @extern function is not verified
  }.ensuring(res => res >= 0 && res * res <= x && x < (res + 1) * (res + 1))
}
