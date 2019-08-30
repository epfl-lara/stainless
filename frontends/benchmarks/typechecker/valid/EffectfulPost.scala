import stainless.lang._

object EffectfulPost {
  case class Foo(var bar: Int)

  def mutateFoo(foo: Foo): Boolean = {
    foo.bar = foo.bar + 1
    foo.bar > 10
  }

  def test = {
    true
  } ensuring { _ =>
    val foo = Foo(0)
    val after = mutateFoo(foo)
    after == false
  }
}
