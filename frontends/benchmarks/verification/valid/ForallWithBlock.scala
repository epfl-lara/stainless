import stainless.lang._

object ForallWithBlock {
  def g(w: BigInt) = true

  def f() = {
    assert(forall((w: BigInt) => { g(w); true }))
  }
}
