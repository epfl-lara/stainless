import stainless._
import stainless.annotation.cCode
import stainless.math._

object InPlaceRefFnCall2 {
  case class Ref[T](var x: T)

  @cCode.`export`
  def f(v: Int): Unit = wrapping {
    // The expression (456, Ref(v + 10)) will be converted to something like:
    // int32_t tmp = v + 10;
    // Tuple2 { ._1 = 456, ._2 = &tmp }
    placeholder((456, Ref(v + 10)))
  }

  def placeholder(r: (Int, Ref[Int])): Unit = {
    ()
  }

  @cCode.`export`
  def main(): Unit = ()
}