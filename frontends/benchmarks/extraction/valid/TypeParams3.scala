import stainless.lang._

object TypeParams3 {
  abstract class Test[A] {
    def something: A
  }

  case class FooBar[Foo, Bar, Baz](foo: Foo, bar: Bar, baz: Baz) extends Test[Bar] {
    def something: Bar = bar
  }

  def foo[Toto](toto: Toto, y: BigInt): Test[Toto] = {
    require(y == 0)
    def bar[Str](fooStr: Str): Test[Toto] = {
      FooBar(fooStr, toto, y)
    }
    bar("FooStr")
  }

  def test = {
    foo(Some("Test"), 0).something == Some("Test")
  }.holds
}
