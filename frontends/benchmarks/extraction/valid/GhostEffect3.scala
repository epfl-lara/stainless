import stainless.lang._
import stainless.annotation._

object GhostEffect3 {

  import stainless.util.Random

  case class Foo(@ghost value: BigInt)

  def bar: Foo = {
    implicit val state = Random.newState
    val rand = Random.nextBigInt(state)
    Foo(rand)
  }

}
