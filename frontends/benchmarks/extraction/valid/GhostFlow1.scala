import stainless.annotation.{ghost => ghostAnnot}
import stainless.lang._
import stainless.collection._

object GhostFlow1 {
  case class Ghost(@ghostAnnot var p: BigInt) {
    def f(x: BigInt) = {
      ghost {
        p = p + 1
      }
    }
  }
}
