import stainless._
import stainless.lang._
import stainless.annotation._

object i1332d {
  @opaque
  @inlineOnce
  def looping_g(i: BigInt): BigInt = {
    require(i >= 0)
    decreases(i)
    looping_g(i)
  }
}