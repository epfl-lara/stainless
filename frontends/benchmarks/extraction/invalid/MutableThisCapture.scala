import stainless.lang._

object MutableThisCapture {
  case class A(val v: BigInt, var m: BigInt) {
    // `g` only accesses the immutable field `v`, so it is valid on its own.
    def g(): BigInt => BigInt = x => v
    // Calling `this.g()` still passes `this` (of mutable type) as an argument,
    // so it should be rejected even though `g` itself is fine.
    def f(): BigInt => BigInt = x => this.g()(x)
  }
}
