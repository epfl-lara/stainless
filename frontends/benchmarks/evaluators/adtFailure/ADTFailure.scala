object ADTFailure {

  case class MyADT(x: BigInt) {
    require(0 <= x && x < 100)
  }

  def ohno: BigInt = MyADT(42).x + MyADT(101).x
}