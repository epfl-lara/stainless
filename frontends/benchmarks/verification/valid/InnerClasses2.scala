import stainless.lang._

object InnerClasses2 {

  abstract class Test {
    def something: BigInt
  }

  def foo(x: Boolean, l: BigInt): Test = {
    require(l > 1)
    def bar(y: Boolean, m: BigInt): Test = {
      require(m > 2)
      def baz(z: Boolean, o: BigInt): Test = {
        require(o > 3)
        case class FooBarBaz(a: Boolean, b: Boolean, c: Boolean) extends Test {
          def something: BigInt = if (a) l else if (b) m else if (c) o else 0
        }
        FooBarBaz(x, y, z)
      }
      baz(false, 4)
    }
    bar(true, 3)
  }

  def test = (foo(false, 2).something == 3).holds
}
