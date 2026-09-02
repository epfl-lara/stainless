import stainless.lang._

object ImmutableFieldCapture {
  case class A(val v: BigInt, var m: BigInt) {
    def g(): BigInt => BigInt = x => v + m
    def f(): BigInt => BigInt = x => this.g()
  }
}
