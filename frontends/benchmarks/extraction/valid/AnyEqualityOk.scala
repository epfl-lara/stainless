import stainless.collection.*
import stainless.lang.*

object AnyEqualityOk:
  def same[T](x: T, y: T): Boolean = x == y

  def numbers(): Boolean = same[Int](5, 5) && same[BigInt](1, 1) && same[(Int, Char)]((1, 'a'), (1, 'a'))

  case class Box[T](x: T)

  def boxes(a: Box[Int], b: Box[Int]): Boolean = a == b

  def wildcard(b: Box[?]): Boolean = true

  def lists(l: List[BigInt]): Boolean = l.contains(1) && l == Nil[BigInt]()

  def related(x: List[Option[BigInt]], y: List[None[BigInt]]): Boolean = x == y

  // Values of type `Any` are fine as long as they are not compared
  case class Holder(a: Any)

  def holder(h: Holder): Boolean = h.a.isInstanceOf[Int]

  abstract class Nat:
    type Repr
    def zero: Repr
    def isZero(n: Repr): Boolean = n == zero

  case class BigNat() extends Nat:
    type Repr = BigInt
    def zero: BigInt = 0

  def emptySet(): Boolean = Set[BigInt]().isEmpty

  def literal(x: BigInt): Boolean = x match
    case 5 => true
    case _ => false
