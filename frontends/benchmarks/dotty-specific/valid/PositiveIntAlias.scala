import stainless.lang._

object PositiveIntAlias {

  type PositiveInt = { x: Int => x > 0 }

  case class Foo(n: PositiveInt) {
    def bar: Int = n
  }

  def test(foo: Foo) = {
    assert(foo.bar > 0)
  }

  def takePos(m: PositiveInt): PositiveInt = {
    if (m + 1 > 0) m + 1 else m
  }

}
