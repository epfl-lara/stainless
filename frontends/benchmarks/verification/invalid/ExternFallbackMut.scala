import stainless.lang._
import stainless.annotation._

object ExternFallbackMut {

  @ignore
  case class ANewHope(var x: BigInt)

  case class Wrapper(
    @extern
    stuff: ANewHope
  ) {

    @extern
    def doStuff(): Unit = {
      stuff.x = 42
    }
  }

  def prop(a: Wrapper) = {
    a.doStuff()
  } ensuring { a == old(a) }

}
