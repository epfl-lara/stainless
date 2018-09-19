import stainless.lang._
import stainless.annotation._

object GhostEffect1 {

  import stainless.util.Random

  case class App(state: Random.State) {
    def doStuff(@ghost ignoreMe: BigInt): BigInt = {
      Random.nextBigInt(state)
    }

    def foo = {
      val rand = Random.nextBigInt(state)
      doStuff(rand)
    }
  }

}
