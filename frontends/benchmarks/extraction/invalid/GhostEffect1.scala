import stainless.lang._
import stainless.annotation._
import stainless.io.State

object GhostEffect1 {

  import stainless.util.Random

  case class App(state: State) {
    def doStuff(@ghost ignoreMe: BigInt): BigInt = {
      Random.nextBigInt(state)
    }

    def foo = doStuff(Random.nextBigInt(state))
  }

}
