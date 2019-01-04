import stainless.lang._

object Assert4 {

  case class T(var x: BigInt) {
    def f() = {
      x = x + 1
      false ==> { assert(false); true }
    }
  }
}
