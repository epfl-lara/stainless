
import stainless.lang._

object SuperCall1 {

  sealed abstract class Base {
    def method(x: BigInt): BigInt
  }

  case class Override() extends Base {
    override def method(x: BigInt): BigInt = {
      x + 1
    }
  }

  def test1(x: Base) = {
    x.method(123) == 124
  }.holds

  def test2 = {
    Override().method(123) == 124
  }.holds

}
