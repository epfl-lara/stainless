
import stainless.lang._
import stainless.annotation._

object ParentInvariant {

  abstract class Foo {
    @law def inv = foo(0) == 0
    def foo(x: BigInt): BigInt
  }

  case class Bar(y: BigInt) extends Foo {
    require(y != 0)
    def foo(x: BigInt): BigInt = y
  }

  case class Baz(y: BigInt) extends Foo {
    require(y == 0)
    def foo(x: BigInt): BigInt = y
  }

  def fail = Bar(12)
  def ok   = Baz(0)

}
