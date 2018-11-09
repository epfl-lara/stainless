import stainless.lang._
import stainless.annotation._

object AccessorMutation1 {

  @mutable
  sealed abstract class Toto {
    var value: BigInt
  }

  case class Foo(var value: BigInt) extends Toto
  case class Bar(var value: BigInt) extends Toto

  sealed abstract class Tata extends Toto
  case class Baz(var value: BigInt) extends Tata

  def t1(toto: Toto) = {
    toto.value = 2
    assert(toto.value == 2)
  }

  def t2(tata: Tata) = {
    tata.value = 2
    assert(tata.value == 2)
  }

}
