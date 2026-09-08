import stainless.lang._
import stainless.collection._

object ErasedFlow2 {
  case class Erased(erased var l: List[BigInt]) {
    def f(x: BigInt) = {
      ghost {
        l = x :: l // Argument to ghost parameter `value` of `ghost` must only have effects on ghost fields
      }
    }
  }
}
