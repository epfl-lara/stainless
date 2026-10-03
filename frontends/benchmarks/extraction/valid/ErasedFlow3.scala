import stainless.lang._
import stainless.annotation.ghost

object ErasedFlow3 {
  case class Erased(erased var x: BigInt) {
    @ghost def f() = {
      val y = x // Right-hand side of non-ghost variable cannot be ghost
    }
  }
}
