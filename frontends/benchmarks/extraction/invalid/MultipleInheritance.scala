
import stainless.lang._
import stainless.annotation._

object MultipleInheritance {

  trait Foo1
  trait Foo2
  case class Bar() extends Foo1 with Foo2

}
