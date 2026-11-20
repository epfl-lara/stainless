import stainless.lang._

// A variant of UnsatisfiablePostcondition where the open class has a field, so that `TypeEncoding`
// encodes it in `Object`
object UnsatisfiablePostconditionField {
  abstract class Absurdity {
    val n: BigInt = 0
    def m: BigInt = {
      (??? : BigInt)
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
