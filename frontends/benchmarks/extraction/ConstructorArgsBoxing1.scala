
import stainless.lang._
import stainless.collection._

object ConstructorArgsBoxing1 {
  case class A()

  sealed abstract class AnyFoo
  case class Foo[T](x: T) extends AnyFoo

  val a: AnyFoo = Foo(A())
}
