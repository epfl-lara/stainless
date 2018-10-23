
import stainless.lang._

object AnonymousClasses3 {

  abstract class MyClass {
    def foo: BigInt
    def bar(x: Option[BigInt]): BigInt
    def baz(y: Boolean): Boolean = !y
  }

  case object normal extends MyClass {
    def foo = 123
    def bar(x: Option[BigInt]) = x.getOrElse(foo)
  }

  def plain = new MyClass {
    def foo = 123
    def bar(x: Option[BigInt]) = x.getOrElse(foo)
  }

  def closing(something: BigInt) = {
    val abc: BigInt = 1

    new MyClass {
      def foo = something + abc
      def bar(x: Option[BigInt]) = x.getOrElse(foo) * something
    }
  }

  val theorem = {
    closing(123).isInstanceOf[MyClass]
  }.holds

  val theorem2 = {
    closing(123).bar(None()) == 15252
  }.holds

}
