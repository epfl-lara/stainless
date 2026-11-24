import stainless.lang._

// A function outside of any class cannot be overridden: it cannot be abstract.
object AbstractMethodBodyFunction {
  def root(x: BigInt): BigInt = {
    require(x >= 0)
    AbstractMethodBody[BigInt]()
  }.ensuring(res => res >= 0 && res * res <= x)
}
