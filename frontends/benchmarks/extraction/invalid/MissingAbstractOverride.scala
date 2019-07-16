import stainless.lang._

object MissingAbstractOverride {

  abstract class Foo {
    def test(x: Int): Int

    def test2(x: Int): Int = {
      require(x > 0)
      (??? : Int)
    } ensuring (_ > 0)
  }

  case class Bar() extends Foo
  // Not well formed definition class Bar extends Foo because abstract methods
  // MissingAbstractOverride.Foo.test, MissingAbstractOverride.Foo.test2 were not overriden

}
