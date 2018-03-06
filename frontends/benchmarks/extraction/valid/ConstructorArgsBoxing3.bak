
import stainless.lang._
import stainless.collection._

object ConstructorArgsBoxing3 {
  sealed abstract class A
  case class B() extends A
  case class C() extends A

  case class Foo[+T](x: T)

  def b: Foo[B] = Foo(B())
  def c: Foo[C] = Foo(C())

  def list0: List[Foo[A]] = List(b, c)

  def list1: List[Foo[Any]] = List(b, c)
}
