import stainless._
import stainless.lang._
import stainless.annotation._

object i1271d {
  @opaque
  @inlineOnce
  def looping_f(x: BigInt): BigInt = {
    require(x >= 0)
    decreases(x)
    looping_f(x + 1)
  }.ensuring(_ => false)
}