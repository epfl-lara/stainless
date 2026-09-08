import stainless.lang._
import stainless.collection._

object ErasedFlow1 {
  case class Erased(erased var p: BigInt) {
    def f(x: BigInt) = {
      ghost {
        p = p + 1
      }
    }
  }
}
