import stainless.lang._

object InnerClasses2 {
  case class Foo(x: Int) {
    def bar(y: Int): Int = {
      case class Bar(a: Int) {
        def test: Int = a + x + y
      }
      Bar(12).test
    }
  }
}
