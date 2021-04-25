import stainless.lang._
import stainless.annotation._
import stainless.io.State

object GhostEffect2 {

  import stainless.util.Random

  def bar(implicit state: State) = {
    @ghost val test = Random.nextBigInt
    ()
  }

}
