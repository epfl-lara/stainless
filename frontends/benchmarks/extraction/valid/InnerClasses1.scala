import stainless.lang._

object InnerClasses1 {

  abstract class Test {
    def something: BigInt
  }

  def foo(x: BigInt, l: BigInt): Test = {
    require(l > 1)
    case class FooBarBaz(a: BigInt) extends Test {
      def something: BigInt = a + l
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

