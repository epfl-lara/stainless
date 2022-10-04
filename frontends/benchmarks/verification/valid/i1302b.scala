import stainless.collection._

object i1302b {
  def f: Unit = {
    val lam = (x: BigInt) => {
      def nasty = x + x
      nasty
    }
    val lam2 = (x: BigInt) => {
      def nasty2 = x + x + x
      nasty2
    }
    assert(lam2(0) == 0)
  }
}