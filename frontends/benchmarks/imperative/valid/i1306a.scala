import stainless._
import stainless.lang._
import stainless.annotation._

object i1306a {
  def root(a: BigInt): BigInt = {
    require(a >= 0)
    var i: BigInt = 0
    def nextSquare = ((i + 1) * (i + 1))
    (while (nextSquare <= a) {
      decreases(a - nextSquare) // termination
      i = i + 1
    }) invariant { i >= 0 && ((i * i) <= a) }
    i
  }.ensuring { root => (root * root) <= a && a < ((root + 1) * (root + 1)) }
}
