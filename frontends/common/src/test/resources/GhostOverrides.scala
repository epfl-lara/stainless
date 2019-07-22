import stainless.lang._
import stainless.annotation._

object GhostOverrides {

  abstract class Test {
    @ghost
    def doStuff(x: BigInt): BigInt
  }

  case class GhostTest() extends Test {
    @ghost
    override def doStuff(x: BigInt): BigInt = {
      x + 1
    }
  }

  case class NonGhostTest() extends Test {
    override def doStuff(x: BigInt): BigInt = {
      x * 2
    }
  }
}

