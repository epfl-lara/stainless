
import stainless.lang._
import stainless.proof._
import stainless.annotation._

object Laws0 {

  abstract class SomeLaw {
    def value: BigInt

    @law
    def lawNotZero: Boolean = {
      value != 0
    }
  }

  case class ConcreteOverride() extends SomeLaw {
    def value = 42

    override def lawNotZero: Boolean = {
      super.lawNotZero && value == 42
    }
  }

  case class ConcreteNoOverride() extends SomeLaw {
    def value = 42
  }
}
