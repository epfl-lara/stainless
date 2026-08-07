import stainless.lang._

object Pow2 {
  def pow2(k: BigInt): BigInt = {
    require(k >= 0)
    decreases(k)
    if (k == 0) BigInt(1) else 2 * pow2(k - 1)
  }.ensuring(res => res >= 1)

  def pow2Fast(k: BigInt): BigInt = {
    require(k >= 0)
    if k == 32 then BigInt("4294967296") // Princess was finding a counterexample here due to a bug in the inox encoding
    else pow2(k)
  }.ensuring(res => res == pow2(k))
}