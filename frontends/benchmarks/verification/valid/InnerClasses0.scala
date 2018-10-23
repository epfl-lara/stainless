import stainless.lang._

object InnerClasses0 {

  abstract class Test {
    def something: BigInt
  }

  def foo(x: BigInt, l: BigInt): Test = {
    require(l > 1)
    case class FooBarBaz(a: BigInt) extends Test {
      def something: BigInt = a + l
    }
    val abc = FooBarBaz(x)
    FooBarBaz(abc.a)
  }

  def test = {
    foo(42, 10).something == BigInt(52)
  }.holds
}
