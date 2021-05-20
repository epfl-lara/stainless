import stainless.lang._
import stainless.annotation._

object MutableTuple {
  case class Foo(var value: BigInt)
  case class Bar(var value: BigInt)

  def t1(pair: (Foo, Bar)) = {
    pair._1.value = 1
    assert(pair._1.value == 1)
  }
}
