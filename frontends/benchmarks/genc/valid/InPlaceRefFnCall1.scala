import stainless._
import stainless.annotation.cCode
import stainless.math._

object InPlaceRefFnCall1 {
  case class Ref[T](var x: T)
  case class Container[T](v: Ref[T])

  @cCode.`export`
  def f(v: Int): Unit = wrapping {
    // The expression Container(Ref(v + 10)) will be converted to something like:
    // int32_t tmp = v + 10;
    // Container { .v = &tmp }
    placeholder(Container(Ref(v + 10)))
  }

  def placeholder(r: Container[Int]): Unit = {
    ()
  }

  @cCode.`export`
  def main(): Unit = ()
}