import stainless.lang._

object ChooseInFieldType {
  // The predicate of the `choose` in the type of `y` can't be satisfied
  case class Empty(x: BigInt, y: { v: BigInt with v == choose((w: BigInt) => w > x && w < x) })
}
