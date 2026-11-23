import stainless.lang.{ghost => ghostExpr, _}
import stainless.annotation._

// Ghost code is erased before the program runs, so `???` can appear anywhere in it.
object UnimplementedGhost {
  @ghost
  def someWitness(x: BigInt): BigInt = {
    require(x >= 0)
    (??? : BigInt)
  }.ensuring(res => res >= x)

  @ghost
  def nested(x: BigInt): BigInt = {
    if (x > 0) x else (??? : BigInt)
  }

  def keep(x: BigInt, @ghost witness: BigInt): BigInt = x

  def test(x: BigInt): BigInt = {
    require(x >= 0)
    @ghost val w = someWitness(x)
    @ghost val f = (y: BigInt) => (??? : BigInt)
    ghostExpr {
      val v = (??? : BigInt)
      assert(w >= x)
      assert(nested(1) == 1)
    }
    keep(x, (??? : BigInt)) + keep(x, someWitness(x))
  }.ensuring(_ == 2 * x)
}
