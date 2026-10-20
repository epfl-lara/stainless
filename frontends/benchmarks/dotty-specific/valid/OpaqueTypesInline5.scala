import stainless.lang._

// Nested inline calls across two objects with opaque type aliases: the proxies of
// the outer inlining are referenced from inside the inner `Inlined` node.
object OpaqueTypesInline5 {
  object A {
    opaque type TA = BigInt
    def fa(x: BigInt): BigInt = x
    inline def ia(x: BigInt): BigInt = this.fa(x) + B.ib(x)
  }

  object B {
    opaque type TB = BigInt
    def fb(x: BigInt): BigInt = x
    inline def ib(x: BigInt): BigInt = this.fb(x)
  }

  def run(x: BigInt): BigInt = {
    A.ia(x)
  }.ensuring(_ == x + x)
}
