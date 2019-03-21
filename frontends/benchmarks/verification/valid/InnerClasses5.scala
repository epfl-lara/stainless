import stainless.lang._
import stainless.annotation._
import stainless.collection._

object InnerClasses5 {

  abstract class Test[A] {
    def something: A
  }

  @inline
  def foo[Foo](x: Foo, y: BigInt): Test[Foo] = {
    require(y == 0)
    def bar[Bar](a: Bar, b: BigInt): Test[Foo] = {
      require(b > 2)
      case class FooBar[Baz](bar: Bar, baz: Baz) extends Test[Foo] {
        def something: Foo = x
      }
      FooBar(a, "Baz")
    }
    bar(List(true, false), 3)
  }

  def test = {
    foo(Some("Test"), 0).something == Some("Test")
  }.holds

}
