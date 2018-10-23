import stainless.lang._

object InnerClasses3 {

  abstract class Test {
    def something: BigInt
  }

  def foo(x: Boolean, l: BigInt): Test = {
    require(l > 1)

    case class FooBarBaz(a: Boolean) extends Test {
      def something: BigInt = {
        case class HelloWorld(b: Boolean) extends Test {
          def something: BigInt = if (FooBarBaz.this.a && b) l else 42
        }
        val hello = HelloWorld(x && this.a)
        hello.something
      }
    }

    FooBarBaz(x)
  }

  def test = foo(false, 2)
}
