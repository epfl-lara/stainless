import stainless.lang._

object IndirectCaptureOfMutableField {
  case class Box(var value: BigInt)
  case class A(val v: BigInt, val m: Box) {
    def f(): BigInt => BigInt = 
      val g = m
      x => g.value
  }
}
