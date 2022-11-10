import stainless._
import stainless.lang._
import stainless.annotation._

object i1271a {
  @opaque
  def looping_f(x: BigInt): Unit = {
    decreases(x)
    require(x >= 0)
    looping_f(x + 1)
  }.ensuring(_ => false)
}