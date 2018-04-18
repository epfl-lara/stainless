
import stainless.lang._
// import stainless.collection._

object AnonymousClasses {

  // abstract class Foo {
  //   def bar: Int
  // }

  // def stuff: Boolean = {
  //   val foo = new Foo {
  //     def bar: Int = 1
  //     val baz: Boolean = true
  //   }

  //   foo.baz
  // }.holds

  abstract class MyClass {
    def foo: BigInt
    def bar(x: Option[BigInt]): BigInt
    def baz(y: Boolean): Boolean = !y
  }

  object normal extends MyClass {
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

  abstract class Monoid[M] {
    def empty: M
    def append(left: M, right: M): M
  }

  val bigIntAddMonoid = new Monoid[BigInt] {
    def empty: BigInt = 0
    def append(left: BigInt, right: BigInt): BigInt = left + right
  }

  // def listMonoid[A]: Monoid[List[A]] = new Monoid[List[A]] {
  //   def empty: List[A] = Nil()
  //   def append(left: List[A], right: List[A]): List[A] = left ++ right
  // }

  // def optionMonoid[A](aMonoid: Monoid[A]): Monoid[Option[A]] = new Monoid[Option[A]] {
  //   def empty: Option[A] = None()
  //   def append(left: Option[A], right: Option[A]): Option[A] = (left, right) match {
  //     case (Some(l), Some(r)) => Some(aMonoid.append(l, r))
  //     case _ => None()
  //   }
  // }

  // case class Box[A](value: A)

  // case class BoxMonoid[X](x: X) extends Monoid[Box[X]] {
  //   def append(left: Box[X], right: Box[X]): Box[X] = Box(x)
  // }

  // def boxMonoid[X](x: X): Monoid[Box[X]] = new BoxMonoid[X](x)

  // def boxMonoid[X](x: X): Monoid[Box[X]] = new Monoid[Box[X]] {
  //   def append(left: Box[X], right: Box[X]): Box[X] = Box(x)
  // }

}

