object Imperative {
  trait Box {
    var v = BigInt(0)
    def load(x: BigInt) = {
      v = x
    }
  }

  case class A(var f: BigInt)
}
