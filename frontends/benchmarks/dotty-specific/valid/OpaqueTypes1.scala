import scala.language.implicitConversions

import stainless.lang._
import stainless.annotation._

object OpaqueTypes1 {

  opaque type Positive = BigInt

  object Positive {
    def apply(b: BigInt): Positive = {
      require(b >= 0)
      b
    }

    def safe(b: BigInt): Option[Positive] = {
      if (b >= 0) Some(b) else None()
    }

    object ops {
      def (p: Positive) toBigInt: BigInt = p
    }
  }

  import Positive.ops._

  def test = {
    val p = Positive(42)
    assert(p.toBigInt == 42)
  }

}
