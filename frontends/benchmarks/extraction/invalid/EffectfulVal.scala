import stainless.io.State

object EffectfulVal {

  import stainless.util.Random

  case class Test(state: State) {
    val rand = Random.nextBigInt(state)
  }

}
