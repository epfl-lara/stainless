import stainless.lang._
import stainless.annotation._
import stainless.io._

object GhostEffect3 {

  import stainless.util.Random

  case class Foo(@ghost value: BigInt)

  def bar: Foo = {
    implicit val state = newState
    Foo(Random.nextBigInt(state))
  }

}
