import stainless.lang._

// Abstract vals whose type is a type member of `this`, inherited by an open subclass
object InheritedTypeMemberVals {
  abstract class Container {
    type T
    val x: T
    def get: T = x
  }

  abstract class Named extends Container {
    val name: BigInt
  }

  case class IntNamed(x: BigInt, name: BigInt) extends Named {
    type T = BigInt
  }

  def nameOf(n: Named): BigInt = n.name

  def test: Unit = {
    val n = IntNamed(1, 2)
    assert(nameOf(n) == 2)
    assert(n.x == 1)
  }
}
