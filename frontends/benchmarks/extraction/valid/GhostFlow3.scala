import stainless.lang._
import stainless.annotation._

object GhostFlow3 {
  case class Ghost(@ghost var x: BigInt) {
    @ghost
    def f() = {
      val y = x // Right-hand side of non-ghost variable cannot be ghost
    }
  }
}
