import stainless.lang._

object ChooseInFieldType {
  // The `choose` in the type of `y` is lifted into a function, and its satisfiability is checked for all `x`
  case class Bounded(x: BigInt, y: { v: BigInt with v <= x + choose((w: BigInt) => true) })

  def bound(b: Bounded): BigInt = b.y - b.x
}
