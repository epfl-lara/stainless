import stainless._
import stainless.lang._
import stainless.annotation._

object PureFnWithInnerFn {
  @pure
  def outer: Unit = {
    def inner: Unit = ()
  }
}