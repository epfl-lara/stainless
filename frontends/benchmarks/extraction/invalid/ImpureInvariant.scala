object ImpureInvariant {
  case class MyImpureClass(var i: BigInt)

  trait MyTrait {
    def take(m: MyImpureClass): BigInt
  }

  case class HasImpureInvariant(mt: MyTrait, mic: MyImpureClass) {
    require(mt.take(mic) == 0)
  }
}