import stainless.lang._

object ImmutableFieldCapture {
  case class A(val v: BigInt, var m: BigInt) {
    // Accessing a val field of immutable type from a mutable class
    // should be allowed in a lambda.
    def f(): BigInt => BigInt = x => v
  }
}
