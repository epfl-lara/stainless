import stainless.lang._
import stainless.io.State

object ErasedEffect1 {

  import stainless.util.Random

  case class App(state: State) {
    def doStuff(erased ignoreMe: BigInt): BigInt = {
      Random.nextBigInt(state)
    }

    def foo = doStuff(Random.nextBigInt(state))
  }

}
