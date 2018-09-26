import stainless.annotation._
import stainless.lang._
import stainless.collection._

object GhostFlow1 {
  case class Ghost(@ghost var p: BigInt) {
    def f(x: BigInt) = {
      ghost {
        p = p + 1
      }
    }
  }
}
