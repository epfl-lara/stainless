import stainless.lang._

// Inline methods defined directly in an object with an opaque type alias: the
// inlined bodies call sibling members through the this-proxy (`Refined$_this.f(x)`),
// and an argument of the opaque type gets the proxied intersection type
// `(p : Refined.Positive) & $proxy.Positive`.
object OpaqueTypesInline2 {
  object Refined {
    opaque type Positive = BigInt

    def f(x: Positive): Positive = x
    def h(x: BigInt): BigInt = x

    inline def Positive(value: BigInt): Positive = f(value)
    inline def viaThis(value: BigInt): BigInt = this.h(value)
    inline def mk(value: BigInt): Positive = value
    inline def unmk(p: Positive): BigInt = p
  }

  def run(x: BigInt): Unit = {
    val nine = Refined.Positive(x)
    val ten = Refined.viaThis(x)
    assert(ten == x)
    val p = Refined.mk(x)
    val q = Refined.unmk(p)
    assert(q == x)
  }
}
