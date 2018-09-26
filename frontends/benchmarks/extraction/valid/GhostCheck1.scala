import stainless.lang._
import stainless.annotation._
import stainless.collection._

object Ghost1 {
  case class Ghost1(
    @ghost var x: BigInt
  ) {
    @ghost
    def f() = {
      val y = x
    }
  }
}

object Ghost2 {
  case class Ghost2(@ghost var p: BigInt) {
    def f(x: BigInt) = {
      ghost {
        p = p + 1
      }
    }
  }
}

