import stainless.lang._

object MissingAbstractOverride {

  abstract class Foo {
    def test(x: Int): Int

    def test2(x: Int): Int = {
      require(x > 0)
      AbstractMethodBody[Int]()
   }.ensuring(_ > 0)
  }

  case class Bar() extends Foo
  // Class Bar does not implement the abstract methods
  // MissingAbstractOverride.Foo.test, MissingAbstractOverride.Foo.test2

}
