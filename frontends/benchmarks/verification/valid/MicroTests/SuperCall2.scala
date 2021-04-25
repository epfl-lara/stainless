
import stainless.lang._

object SuperCall2 {

  sealed abstract class Base {
    def double(x: BigInt): BigInt = x * 2
  }

  case class Override() extends Base {
    override def double(x: BigInt): BigInt = {
      super.double(x + 1) + 42
    }
  }

  case class NoOverride() extends Base

  def test1 = {
    NoOverride().double(10) == 20
  }.holds

  def test2 = {
    Override().double(10) == 64
  }.holds

}
