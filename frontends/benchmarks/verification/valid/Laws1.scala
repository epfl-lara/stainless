
import stainless.lang._
import stainless.proof._
import stainless.annotation._

object Laws1 {

  abstract class SomeLaw {
    def value: BigInt

    @law
    def lawNotZero: Boolean = {
      value != 0
    }
  }

  abstract class RefinedLaw extends SomeLaw {
    @law
    override def lawNotZero: Boolean = {
      value > 1
    }
  }

  case class ConcreteOverride() extends RefinedLaw {
    def value = 42

    override def lawNotZero: Boolean = {
      value == 42
    }
  }

  case class ConcreteNoOverride() extends RefinedLaw {
    def value = 42
  }
}
