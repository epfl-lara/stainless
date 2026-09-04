import stainless.lang._
import stainless.io.State

object ErasedEffect2 {

  import stainless.util.Random

  def bar(implicit state: State) = {
    erased val test = Random.nextBigInt
    ()
  }

}
