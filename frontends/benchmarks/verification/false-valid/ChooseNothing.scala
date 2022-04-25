import stainless.lang._
import stainless.annotation._

// A variant of Countable2
object ChooseNothing {

  def theorem() = {
    val e: Nothing = choose((x: Nothing) => true)
    assert(false)
    ()
  }
}
