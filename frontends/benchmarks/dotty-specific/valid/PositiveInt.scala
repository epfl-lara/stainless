
import stainless.lang._

object PositiveInt {

  case class Foo(n: { m: Int => m > 0 }) {
    def bar: Int = n
  }

  def test(foo: Foo) = {
    assert(foo.bar > 0)
  }

}
