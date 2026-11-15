import stainless.lang._
import stainless.annotation._

// `@dropVCs` invariants are assumed, but not checked when values are built
object UncheckedInvariant {

  case class Positive(x: BigInt) {
    @dropVCs @invariant
    def positive = x > 0

    @invariant
    def not42 = x != 42
  }

  // only `not42` is checked
  def build = Positive(-1)

  def use(p: Positive) = {
    assert(p.x > 0)
  }
}
