import stainless.lang._
import stainless.io.State

object ErasedEffect2 {

  import stainless.util.Random

  def bar(implicit state: State) = {
    val rand = Random.nextBigInt
    erased val test = rand + 1
    ()
  }

}
