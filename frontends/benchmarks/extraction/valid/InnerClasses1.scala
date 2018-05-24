import stainless.lang._

object InnerClasses1 {

  abstract class Test {
    def something: BigInt
  }

  def foo(x: A, l: BigInt): Test = {
    require(l > 1)
    case class FooBarBaz(a: A) extends Test {
      def something: BigInt = l
    }
    FooBarBaz(x)
  }

  def bar: BigInt = {
    case class Stuff() {
      def hello: BigInt = Some(BigInt(42)).get
    }
    Stuff().hello
  }
}

