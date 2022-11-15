import stainless._
import stainless.lang._
import stainless.annotation._

object i1332b {
  @opaque
  @inlineOnce
  def looping_f(i: BigInt): BigInt = {
    require(i >= 0)
    decreases(i)
    val x = looping_f(looping_f(i) - i - 1)
    x + 1
  }.ensuring(_ == i + 1)
}