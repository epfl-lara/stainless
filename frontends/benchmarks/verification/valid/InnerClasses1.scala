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

  def prop = {
    foo(1, 2).something == 3
  }.holds

}
