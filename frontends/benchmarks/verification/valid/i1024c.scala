import stainless.lang.*

object i1024c:

  sealed abstract class List[T]:
    def size: BigInt = this match
      case Nil() => BigInt(0)
      case h :: t => 1 + t.size

  case class Cons[T](h: T, t: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  object :: :
    def unapply[A](l: List[A]): Option[(A, List[A])] = l match
      case Nil() => None()
      case Cons(x, xs) => Some((x, xs))
