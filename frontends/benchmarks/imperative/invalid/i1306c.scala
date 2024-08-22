import stainless._
import stainless.lang._
import stainless.annotation._

object i1306c {
  def root(a: BigInt): BigInt = {
    require(a >= 0)
    var i: BigInt = 0
    def nextSquare = ((i + 1) * (i + 1))
    def incI(x: BigInt, y: BigInt) = i += x + y
    (while (nextSquare <= a) {
      decreases(a - nextSquare)
      val iBefore = i
      incI(a, nextSquare)
      assert(i == iBefore) // No!
      i = i + 1
    }) invariant { i >= 0 && ((i * i) <= a) }
    i
  }.ensuring { root => (root * root) <= a && a < ((root + 1) * (root + 1)) }
}
