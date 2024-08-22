import stainless._
import stainless.lang._
import stainless.annotation._

object i1306b {
  def root1(a: BigInt): BigInt = {
    require(a >= 0)
    var i: BigInt = 0
    def nextSquare = ((i + 1) * (i + 1))
    def accessI(x: BigInt, y: BigInt) = i + x + y
    def modifyI(x: BigInt, y: BigInt) = { i += x + y }
    (while (nextSquare <= a) {
      decreases(a - nextSquare)
      val z = accessI(a, nextSquare)
      assert(z == i + a + (i + 1) * (i + 1))
      val w = accessI(a, i)
      modifyI(a, -a)
      assert(w == i + a + i)
      i = i + 1
    }) invariant { i >= 0 && ((i * i) <= a) }
    i
  }.ensuring { root => (root * root) <= a && a < ((root + 1) * (root + 1)) }

  // Variant that increments `i` with `modifyI`
  def root2(a: BigInt): BigInt = {
    require(a >= 0)
    var i: BigInt = 0
    def nextSquare = ((i + 1) * (i + 1))
    def accessI(x: BigInt, y: BigInt) = i + x + y
    def modifyI(x: BigInt, y: BigInt) = { i += x + y }
    (while (nextSquare <= a) {
      decreases(a - nextSquare)
      val z = accessI(a, nextSquare)
      assert(z == i + a + (i + 1) * (i + 1))
      val w = accessI(a, i)
      modifyI(a, -a)
      assert(w == i + a + i)
      modifyI(0, 1)
    }) invariant { i >= 0 && ((i * i) <= a) }
    i
  }.ensuring { root => (root * root) <= a && a < ((root + 1) * (root + 1)) }
}
