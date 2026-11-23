import stainless.lang._
import stainless.annotation._

// Calling an abstract method through `super` is rejected in ghost code too: the
// call would otherwise prove the property with the contract that it has to establish.
object AbstractMethodBodyGhostSuperCall {
  abstract class Shape {
    def area: BigInt

    @ghost
    def areaIsPositive: Unit = {
      AbstractMethodBody[Unit]()
    }.ensuring(_ => area >= 0)
  }

  case class Hole() extends Shape {
    override def area: BigInt = -1

    @ghost
    override def areaIsPositive: Unit = {
      super.areaIsPositive
    }.ensuring(_ => area >= 0)
  }
}
