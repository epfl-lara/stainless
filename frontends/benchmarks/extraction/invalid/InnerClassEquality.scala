
object InnerClassInequality {

  abstract class Test {
    def bar: BigInt
  }

  def f(x: BigInt): Test = {
    case class Foo(y: BigInt) extends Test {
      def bar = x
    }
    Foo(12)
  }

  def prop(a: Test, b: Test) = {
    require(a != b)
    a.bar + b.bar
  }

  def oops = {
    prop(f(1), f(2)) // Precond. verifies but crashes with scalac
  }

}
