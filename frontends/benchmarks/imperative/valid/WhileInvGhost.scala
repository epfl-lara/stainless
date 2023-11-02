import stainless.lang.{WhileDecorations => _, _}
import stainless.annotation._
import StaticChecks._

object WhileInvGhost {
  @ghost
  def inv(x: BigInt): Boolean = x >= 0

  def appendBits(x: BigInt): Unit = {
    require(x >= 0)
    var i: BigInt = 0
    (while (i < x) {
      decreases(x - i)
      i += 1
    }).invariant(inv(i))
  }
}