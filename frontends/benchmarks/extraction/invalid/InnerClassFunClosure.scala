
object InnerClassFunClosure {

  abstract class Foo {
    def bar: Int
  }

  def mkFoo(n: Int) = {
    def go(x: Int): Int = {
      x + n
    }

    new Foo {
      def bar = go(100)
    }
  }

}
