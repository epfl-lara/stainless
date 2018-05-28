import stainless.lang._

object InnerClasses4 {

  case class Foo(x: Int) {
    def bar(y: Int): Int = {
      case class Bar() {
        def test: Int = x + y
      }
      Bar().test
    }
  }

  def test = (Foo(40).bar(2) == 42).holds

}
