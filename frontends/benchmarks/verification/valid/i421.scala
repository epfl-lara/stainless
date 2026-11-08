import stainless.annotation.*
import stainless.lang.*

object i421:

  @mutable trait A

  trait B extends A:
    var x: BigInt

    final def f() =
      def g(j: BigInt) =
        require(j == 0)
        x = 0

      g(0)
