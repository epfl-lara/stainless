import stainless.lang._
import stainless.annotation._

object GhostEffect2 {

  import stainless.util.Random

  def bar(implicit state: Random.State) = {
    val rand = Random.nextBigInt
    @ghost val test = rand + 1
    ()
  }

}
