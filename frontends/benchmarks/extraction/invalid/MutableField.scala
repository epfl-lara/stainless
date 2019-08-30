object MutableField {
  case class Container(var v: BigInt) {
    def load(x: BigInt) = {
      v = x
    }
  }

  abstract class Box {
    val c = Container(0)
    def load(x: BigInt) = c.load(x)
  }

  case class Nat() extends Box {
    require(c.v >= 0)         // should not be allowed (?)

    def extract(): BigInt = {
      c.v
    } ensuring(_ >= 0)
  }

  def theorem() = { 
    val n = Nat()
    n.load(-1)
    assert(n.extract() == 0)  // should be -1
  }
}
