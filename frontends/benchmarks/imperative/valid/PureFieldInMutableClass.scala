import stainless.annotation.{ pure, opaque, mutable }

object PureFieldInMutableClass {
  @mutable final case class MutableClass(var mutableField: BigInt){
    lazy val PUREVALUE: BigInt = computeValue()
    @pure @opaque def computeValue(): BigInt = 42

  }


}