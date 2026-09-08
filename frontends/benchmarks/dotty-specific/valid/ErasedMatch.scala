
import stainless.lang._
import stainless.annotation.ghost

object ErasedMatch {

  case class Foo(erased value: Option[BigInt])

  def nonErasedMatch(foo: Foo) = {
    foo match { // should fail
      case Foo(Some(a)) => true
      case Foo(_) => false
    }
  }

  @ghost def erasedMatch(foo: Foo) = {
    foo match {
      case Foo(Some(a)) => true
      case Foo(_) => false
    }
  }
}
