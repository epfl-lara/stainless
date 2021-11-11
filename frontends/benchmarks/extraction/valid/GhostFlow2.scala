import stainless.annotation.{ghost => ghostAnnot}
import stainless.lang._
import stainless.collection._

object GhostFlow2 {
  case class Ghost(@ghostAnnot var l: List[BigInt]) {
    def f(x: BigInt) = {
      ghost {
        l = x :: l // Argument to ghost parameter `value` of `ghost` must only have effects on ghost fields
      }
    }
  }
}
