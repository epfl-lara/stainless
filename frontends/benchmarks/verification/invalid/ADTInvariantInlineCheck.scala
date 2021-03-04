
import stainless.lang._
import stainless.annotation._
import stainless.collection._

object inlineInv {

  @inlineInvariant
  sealed abstract class Toto

  case class Foo(x: BigInt) extends Toto {
    require(x > 10)
  }

  def bad: Toto = {
    Foo(5)
  }

  def ok: Toto = {
    Foo(15)
  }

}
