
import stainless.lang._
import stainless.proof._
import stainless.annotation._

object Laws1 {

  abstract class A {
    def value: BigInt

    @law
    def lawNotZero: Boolean = {
      value != 0
    }
  }

  abstract class B extends A {
    override def lawNotZero: Boolean = {
      value == 0
    }
  }

  case class C() extends B {
    def value = 0
  }
}
