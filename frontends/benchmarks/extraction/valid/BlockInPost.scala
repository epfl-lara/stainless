import stainless.lang._
import stainless.proof._

object Foo {
  def foo(): Boolean = {
    true
  }.holds {
    check(1 == 1)
    true
  }
}
