import stainless._
import stainless.lang._
import stainless.annotation._

object RecursiveOpaque2 {
  @opaque
  def f(x: BigInt): BigInt = {
    require(x >= 0)
    decreases(x)
    if (x == 0) BigInt(0)
    else {
      val y = f(x - 1)
      assert(y == 0) // No, because we only know y >= 0, we do not know f's body (even for recursive calls)
      y
    }
  }.ensuring(_ >= 0)
}
