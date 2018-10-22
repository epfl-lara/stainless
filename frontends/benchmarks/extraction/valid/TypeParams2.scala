import stainless.lang._

object TypeParams2 {
  abstract class Test[A] {
    def something: A
  }

  case class FooBar[Baz, Foo, Bar](bar: Bar, baz: Baz, x: Foo) extends Test[Foo] {
    def something: Foo = x
  }

  def foo[Foo](x: Foo, y: BigInt): Test[Foo] = {
    require(y == 0)
    def bar[Bar](a: Bar, b: BigInt): Test[Foo] = {
      require(b > 2)
      FooBar(a, "Baz", x)
    }
    bar((x: BigInt) => x + 1, 3)
  }

  def test = {
    foo(Some("Test"), 0).something == Some("Test")
  }.holds
}
