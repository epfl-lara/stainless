import stainless.lang._

object ParadoxInvariant {
  // A sort whose invariant quantifies over the sort itself: if no T exists, then T(0) satisfies
  // the invariant and is a T, and if some T exists, its invariant says that no T exists.
  //
  // Inox rejects such invariants, which quantify over values that depend on the sort's own.
  case class T(x: BigInt) {
    require(forall((t: T) => false))
  }

  // No T exists.
  def noT: Unit = {
    ()
  }.ensuring(_ => forall((t: T) => false))

  // But some T exists: otherwise T(0) would be one.
  def someT: Unit = {
    if (forall((t: T) => false)) {
      val t = T(0)
    }
  }.ensuring(_ => !forall((t: T) => false))

  def paradox: Unit = {
    noT
    someT
    assert(false)
  }
}
