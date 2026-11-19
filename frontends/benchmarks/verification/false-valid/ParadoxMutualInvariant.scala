import stainless.lang._

object ParadoxMutualInvariant {
  // The paradox of ParadoxInvariant through two sorts: an A exists iff no B exists, and a B
  // exists iff some A exists.
  case class A(x: BigInt) {
    require(forall((b: B) => false))
  }

  case class B(a: A)

  // No B exists.
  def noB: Unit = {
    ()
  }.ensuring(_ => forall((b: B) => false))

  // But some B exists: otherwise B(A(0)) would be one.
  def someB: Unit = {
    if (forall((b: B) => false)) {
      val b = B(A(0))
    }
  }.ensuring(_ => !forall((b: B) => false))

  def paradox: Unit = {
    noB
    someB
    assert(false)
  }
}
