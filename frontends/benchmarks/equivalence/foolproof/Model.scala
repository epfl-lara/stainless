import stainless.collection._
import stainless.lang._

// Tests whether `choose` matching avoidance do not get fooled by functions named `choose`.
// See max3 for explanation on this "choose matching avoidance"
object Model {
  def choose(x: BigInt, y: BigInt): BigInt = {
    decreases(if (x <= 0) BigInt(0) else x)
    if (x <= 0) y
    else if (y <= 0) x
    else choose(x - 1, y - 1)
  }

  def funnyZip(xs: List[BigInt], ys: List[BigInt]): List[BigInt] = {
    decreases(xs)
    (xs, ys) match {
      case (_, Nil()) => Nil()
      case (Nil(), _) => Nil()
      case (x :: xs, y :: ys) => choose(x, y) :: funnyZip(xs, ys)
    }
  }
}
