object ConcreteParentVar {
  class C(var x: BigInt)
  case class D(y: BigInt) extends C(y)
}
