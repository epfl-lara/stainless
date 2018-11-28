
import stainless.lang._

object SuperCall6 {

  sealed abstract class Base {
    def method1(x: BigInt): BigInt = x
  }

  case class Override() extends Base {
    override def method1(x: BigInt): BigInt = x + 1
    def method2(x: BigInt): BigInt = super.method1(x)
  }

  def test1 = {
    Override().method1(123) == 124
  }

  def test2 = {
    Override().method2(123) == 123
  }.holds

}
