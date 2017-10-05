
import stainless.lang._
import stainless.collection._

object ConstructorArgsBoxing2 {
  case class A()
  case class B()

  sealed abstract class AnyFoo
  case class Foo[T](x: T) extends AnyFoo

  val a: AnyFoo = Foo(A())
  val b: AnyFoo = Foo(B())

  val list0: List[AnyFoo] = List(a, b)
}
