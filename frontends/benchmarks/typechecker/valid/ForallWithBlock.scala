import stainless.lang._

object ForallWithBlock {
  def g(w: BigInt) = true

  // TYPEFIX: forall

  // def f() = {
  //   assert(forall((w: BigInt) => { g(w); true }))
  // }
}
