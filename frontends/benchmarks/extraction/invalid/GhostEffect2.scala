import stainless.lang._
import stainless.annotation._

object GhostEffect2 {

  import stainless.util.Random

  def bar(implicit state: Random.State) = {
    @ghost val test = Random.nextBigInt
    ()
  }

}
