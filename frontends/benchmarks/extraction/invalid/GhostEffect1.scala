import stainless.lang._
import stainless.annotation._

object GhostEffect1 {

  import stainless.util.Random

  case class App(state: Random.State) {
    def doStuff(@ghost ignoreMe: BigInt): BigInt = {
      Random.nextBigInt(state)
    }

    // def foo = doStuff(Random.nextBigInt(state))

    def bar = {
      @ghost val test = Random.nextBigInt(state)
    }
  }

}
