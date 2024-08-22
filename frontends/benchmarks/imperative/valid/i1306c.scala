import stainless._
import stainless.lang._
import stainless.annotation._

object i1306c {
  // Like coal power plants, lot of energy lost for little gain...
  def laboriousIdentity1(a: BigInt): BigInt = {
    require(a >= 0)
    var i: BigInt = 0
    def nextIncrement = i + 1
    def accessI(x: BigInt, y: BigInt) = i + x + y
    def modifyI(x: BigInt, y: BigInt) = { i += x + y }
    (while (nextIncrement <= a) {
      decreases(a - nextIncrement)
      val z = accessI(a, nextIncrement)
      assert(z == i + a + i + 1)
      val w = accessI(a, i)
      modifyI(a, -a)
      assert(w == i + a + i)
      i = i + 1
    }) invariant { i >= 0 && i <= a }
    i
 }.ensuring { _ == a }

  // Variant that increments `i` with `modifyI`
  def laboriousIdentity2(a: BigInt): BigInt = {
    require(a >= 0)
    var i: BigInt = 0
    def nextIncrement = i + 1
    def accessI(x: BigInt, y: BigInt) = i + x + y
    def modifyI(x: BigInt, y: BigInt) = { i += x + y }
    (while (nextIncrement <= a) {
      decreases(a - nextIncrement)
      val z = accessI(a, nextIncrement)
      assert(z == i + a + i + 1)
      val w = accessI(a, i)
      modifyI(a, -a)
      assert(w == i + a + i)
      modifyI(0, 1)
    }) invariant { i >= 0 && i <= a }
    i
 }.ensuring { _ == a }
}
