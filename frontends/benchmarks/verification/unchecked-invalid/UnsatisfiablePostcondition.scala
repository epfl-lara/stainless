import stainless.lang._

// A variant of ChooseEmpty without laws: no implementation of `Absurdity` can meet the
// postcondition of `m`, so `Absurdity` may have no values.
object UnsatisfiablePostcondition {

  trait Absurdity {
    def m: BigInt = {
      AbstractMethodBody[BigInt]()
    }.ensuring(_ => false)
  }

  def lemma(a: Absurdity): Boolean = {
    a.m
    false
  }.holds

  def theorem() = {
    if (forall((x: Absurdity) => false))
      assert(false)
    else {
      val e: Absurdity = choose((x: Absurdity) => true)
      assert(lemma(e))
      assert(false)
    }
  }
}
