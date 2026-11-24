import stainless.lang.{ghost => ghostExpr, _}
import stainless.annotation._

// `???` must be unreachable in ghost code too, even though it is erased:
// it would otherwise stand for a value that may not exist.
object UnimplementedGhost {
  @ghost
  def someWitness(x: BigInt): BigInt = {
    require(x >= 0)
    (??? : BigInt)
  }.ensuring(res => res >= x)

  def keep(x: BigInt, @ghost witness: BigInt): BigInt = x

  def binding(x: BigInt): BigInt = {
    @ghost val w = (??? : BigInt)
    x
  }

  def block(x: BigInt): BigInt = {
    ghostExpr {
      val v = (??? : BigInt)
      assert(v == v)
    }
    x
  }

  def argument(x: BigInt): BigInt = {
    keep(x, (??? : BigInt))
  }.ensuring(_ == x)
}
