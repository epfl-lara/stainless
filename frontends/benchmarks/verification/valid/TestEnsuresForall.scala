import stainless.annotation.*
import stainless.lang.{ghost => ghostExpr, *}
import stainless.lang.StaticChecks.*
import stainless.lang.Ensures.*
import stainless.lang.Quantifiers.*
object TestEnsuresForall {

  // Opaque Forall test

  def commutes[D](op: (D,D) => D)(d1: D, d2: D): Boolean = {
    op(d1, d2) == op(d2, d1)
  }

  def three[D](op: (D, D) => D, d1: D, d2: D, d3: D) = {
    require(Forall2(commutes(op)))
    ghostExpr:
      Forall2of(commutes(op))(d1, op(d2, d3))
      Forall2of(commutes(op))(d2, d3)
  }.ensuring(_ => op(d1, op(d2, d3)) == op(op(d3, d2), d1))

  // ensures test

  def increasing(x: BigInt, res: BigInt): Boolean = {
    ! (x >= 0) || (res >= x)
  }

  @opaque
  def twice(f: BigInt => BigInt, x: BigInt): BigInt = {
    require(0 <= x && ensures(f, increasing))
    ghostExpr {
      ensuresOf(f, increasing)(x)
      ensuresOf(f, increasing)(f(x))
    }
    f(f(x))
  }.ensuring(res => res >= x)

  def inc(x: BigInt): BigInt = x + 1

  // externally establish given property of a function
  @ghost @opaque
  def incIncreasing: Unit = {
    unfold(ensures(inc, increasing))
  }.ensuring(_ => ensures(inc, increasing))

  // now we can call twice, ensures precondition is not unfolded

  def testInc(x: BigInt): BigInt = {
    require(100 <= x)
    ghostExpr(incIncreasing)
    twice(inc, x)
  }.ensuring(res => 100 <= res)

}
