import stainless.lang._

object BreakImperative {
  case class Toto(var x: BigInt) {
    def inc(): Unit = {
      x += 1
   }.ensuring { _ =>
      old(this).x += 1
      old(this).x == x
    }
  }
}
