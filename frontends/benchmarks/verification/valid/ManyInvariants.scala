import stainless.lang._
import stainless.annotation._

object ManyInvariants {

  case class Foo(x: Int) {
    @invariant
    def positive = x > 0

    @invariant
    def not42 = x != 42
  }

  def test = {
    Foo(1)
  }

}

