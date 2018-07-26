
import stainless.lang._

object SuperCall {

  sealed abstract class Base {
    def method(x: BigInt): BigInt = x
  }

  case class Override() extends Base {
    override def method(x: BigInt): BigInt = {
      super.method(x) + 1
    }
  }

}
