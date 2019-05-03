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
  }

  //   def safe(b: BigInt): Option[Positive] = {
  //     if (b >= 0) Some(b) else None()
  //   }

  //   object ops {
  //     @library
  //     def (p: Positive) toBigInt: BigInt = p ensuring { _ >= 0 }
  //   }
  // }

  // import Positive.ops._

  // def test(p: Positive) = {
  //   assert(p.toBigInt >= 0)
  // }

}
