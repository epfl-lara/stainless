import stainless.lang._

// Class-typed fields that the type test of their class skips, as they mention none of its type parameters
object FixedFields {
  sealed abstract class Lst[+T]
  case object Nl extends Lst[Nothing]
  final case class Cns[+T](h: T, t: Lst[T]) extends Lst[T]

  // A field of a class type with no type parameter of its class
  case class Box[+A](fixed: Lst[BigInt], value: A)

  def head(b: Box[BigInt]): BigInt = b.fixed match {
    case Nl => 0
    case Cns(h, _) => h
  }

  sealed abstract class IntList
  case object INil extends IntList
  final case class ICons(h: BigInt, t: IntList) extends IntList

  def second(l: IntList): BigInt = l match {
    case INil => 0
    case ICons(_, t) => t match {
      case INil => 0
      case ICons(h, _) => h
    }
  }
}
