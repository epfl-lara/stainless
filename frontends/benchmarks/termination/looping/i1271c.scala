import stainless._
import stainless.lang._
import stainless.annotation._

object i1271c {
  @opaque
  def looping_f(x: BigInt): Unit = {
    require(x >= 0)
    looping_g(x)
  }

  @opaque
  def looping_g(x: BigInt): Unit = {
    require(x >= 0)
    looping_h(x)
  }

  @opaque
  def looping_h(x: BigInt): Unit = {
    require(x >= 0)
    looping_f(x)
  }
}