import stainless.lang._
import stainless.annotation._
import stainless.io.State

object GhostEffect2 {

  import stainless.util.Random

  def bar(implicit state: State) = {
    val rand = Random.nextBigInt
    @ghost val test = rand + 1
    ()
  }

}
