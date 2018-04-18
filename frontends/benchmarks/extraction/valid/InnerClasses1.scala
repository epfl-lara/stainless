import stainless.lang._

object InnerClasses1 {

  abstract class Test {
    def something: BigInt
  }

  def foo[A](x: A, l: BigInt): Test = {
    require(l > 1)
    case class FooBarBaz(a: A) extends Test {
      def something: BigInt = l
    }
    FooBarBaz(x)
  }

  abstract class Bar {
    def hello: BigInt
  }

  def bar: BigInt = {
    case class Stuff() extends Bar {
      def hello: BigInt = 42
    }
    Stuff().hello
  }
}

