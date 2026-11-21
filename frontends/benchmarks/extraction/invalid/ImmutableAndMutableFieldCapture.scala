import stainless.lang._

object ImmutableAndMutableFieldCapture {
  case class A(val v: BigInt, var m: BigInt) {
    def f(): BigInt => BigInt = x => v + m
  }
}
