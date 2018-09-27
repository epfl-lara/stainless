import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.lang.StaticChecks._

object GhostAssert {

  case class Ghost(@ghost p: BigInt) {

    def f(x: BigInt) = {
      assert(p + x > 0)
      g(x)
    }

    def g(x: BigInt) = {
      require(p + x > 0)
      x
    }

    def h(x: BigInt) = {
      f(x)
    } ensuring { res => res + p > 0 }
  }

}
