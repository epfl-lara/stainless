import stainless.lang._
import stainless.io._

object ErasedEffect3 {

  import stainless.util.Random

  case class Foo(erased value: BigInt)

  def bar: Foo = {
    implicit val state = newState
    val rand = Random.nextBigInt(state)
    Foo(rand)
  }

}
