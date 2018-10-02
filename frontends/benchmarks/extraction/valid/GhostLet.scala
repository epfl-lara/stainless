import stainless.annotation._
import stainless.lang.StaticChecks._

object GhostLet {
  case class A() {
    def |:(x: Int): Boolean = true
  }

  object A {
    def f(@ghost x: Int, e: A) = assert(x |: e)
  }
}
