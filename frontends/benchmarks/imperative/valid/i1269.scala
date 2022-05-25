import stainless._
import stainless.lang._
import StaticChecks._

object i1269 {
  case class Box(var value: Int)

  def outer1(b: Box): Unit = {
    require(b.value == 123)

    def inner1a: Unit = ().ensuring(_ => snapshot(b).value == 123)

    def inner1b(v: Int): Unit = {
      require(snapshot(b).value == v)
      assert(v == 123)
    }
  }

  def outer2(b: Box): Unit = {
    require(b.value == 123)

    def inner2: Unit = {
      b.value = 456
    }.ensuring(_ => snapshot(b).value == 456)
  }
}