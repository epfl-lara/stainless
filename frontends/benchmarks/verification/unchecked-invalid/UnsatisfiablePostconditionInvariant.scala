import stainless.lang._

// A variant of UnsatisfiablePostcondition where the open class has an invariant
object UnsatisfiablePostconditionInvariant {

  abstract class Absurdity {
    require(true)

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
