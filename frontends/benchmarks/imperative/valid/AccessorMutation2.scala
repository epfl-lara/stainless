import stainless.lang._
import stainless.annotation._

object AccessorMutation2 {

  case class IntBox(var value: BigInt)

  case class ArrayBox(var array: Array[IntBox])

  @mutable
  sealed abstract class Toto {
    val box: ArrayBox
  }

  case class Foo(box: ArrayBox) extends Toto
  case class Bar(box: ArrayBox) extends Toto

  sealed abstract class Tata extends Toto
  case class Baz(box: ArrayBox) extends Tata

  def t1(toto: Toto) = {
    require(toto.box.array.length > 0)
    toto.box.array(0).value = 2
    assert(toto.box.array(0).value == 2)
  }

  def t2(tata: Tata) = {
    require(tata.box.array.length > 0)
    tata.box.array(0).value = 2
    assert(tata.box.array(0).value == 2)
  }

}

