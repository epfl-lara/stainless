
import stainless.lang._

object InnerClasses3 {

  abstract class Foo {
    def test: BigInt
  }

  def foo = {
    abstract class Bar extends Foo {
      override def test = 41
    }

    case class Baz() extends Bar {
      override def test = super.test + 1
    }

    Baz().test
  }

  def prop = (foo == 42).holds

}
