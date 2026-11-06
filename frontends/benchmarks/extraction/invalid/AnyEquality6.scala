object AnyEquality6:
  abstract class Nat:
    type Repr
    def zero: Repr
    def isZero(n: Repr): Boolean = n == zero

  case class AnyNat() extends Nat:
    type Repr = Any
    def zero: Any = 0

object AnyEquality6Field:
  abstract class Container:
    type Elem
    def elem: Elem
    def contains(x: Elem): Boolean = elem == x

  case class AnyContainer(elem: Any) extends Container:
    type Elem = Any
