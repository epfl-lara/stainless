import stainless.lang._
import stainless.annotation._

// The invariants without `@dropVCs` are still checked when values are built
object UncheckedInvariantMixed {

  case class Positive(x: BigInt) {
    @dropVCs @invariant
    def positive = x > 0

    @invariant
    def not42 = x != 42
  }

  def build = Positive(42)
}
