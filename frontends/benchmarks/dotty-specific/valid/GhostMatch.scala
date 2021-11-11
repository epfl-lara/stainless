
import stainless.lang._
import stainless.annotation._

object GhostMatch {

  case class Foo(@ghost value: Option[BigInt])

  def nonGhostMatch(foo: Foo) = {
    foo match { // should fail
      case Foo(Some(a)) => true
      case Foo(_) => false
    }
  }

  @ghost def ghostMatch(foo: Foo) = {
    foo match {
      case Foo(Some(a)) => true
      case Foo(_) => false
    }
  }
}
