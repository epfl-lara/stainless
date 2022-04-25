import stainless.lang._
import stainless.annotation._

// A variant of Countable2
object ChooseEmpty {

  trait Absurdity {
    @law
    def yes: Boolean = 1 == 2
  }

  def lemma(a: Absurdity) = {
    assert(a.yes)
    false
  }.holds

  // Same as Countable2.theorem
  def theorem() = {
    if (forall((x: Absurdity) => false))
      assert(false) // Inox assumes every type is not empty
    else {
      val e: Absurdity = choose((x: Absurdity) => true)
      assert(lemma(e))
      assert(false)
    }
  }
}
