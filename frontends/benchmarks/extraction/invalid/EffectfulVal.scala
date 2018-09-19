
object EffectfulVal {

  import stainless.util.Random

  case class Test(state: Random.State) {
    val rand = Random.nextBigInt(state)
  }

}
