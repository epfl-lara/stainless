import stainless.lang._

object ParadoxInvariant {
  // A sort whose invariant quantifies over the sort itself: if no T exists, then T(0) satisfies
  // the invariant and is a T, and if some T exists, its invariant says that no T exists.
  //
  // Inox lets sorts with invariants be empty, but not T: to show that no T exists, it takes a
  // value of T's underlying sort, whose invariant then holds, so the value is a T.
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
