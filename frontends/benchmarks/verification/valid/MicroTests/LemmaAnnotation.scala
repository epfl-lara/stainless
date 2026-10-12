import stainless.lang.{ghost => ghostExpr, _}
import stainless.annotation._

object LemmaAnnotation {
  def sum(n: BigInt): BigInt = {
    require(n >= 0)
    decreases(n)
    if (n == 0) BigInt(0) else n + sum(n - 1)
  }

  // @lemma is a shortcut for @ghost @pure @inlineOnce @opaque
  @lemma
  def sumGeq(n: BigInt): Unit = {
    require(n >= 0)
    decreases(n)
    if (n > 0) sumGeq(n - 1)
  }.ensuring(_ => sum(n) >= n)

  def useLemma(n: BigInt): BigInt = {
    require(n >= 0)
    ghostExpr(sumGeq(n))
    sum(n)
  }.ensuring(res => res >= n)
}
