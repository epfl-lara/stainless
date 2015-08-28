import leon.lang._

object SizeInc {
  
  abstract class List[A]
  case class Cons[A](head: A, tail: List[A]) extends List[A]
  case class Nil[A]() extends List[A]

  def failling_1[A](x: List[A]): Int => Int = {
    (i: Int) => x match {
      case Cons(head, tail) => 1 + failling_1(tail)(i)
      case Nil() => i
    }
  } ensuring { res => forall((a: Int) => res(a) > 0) }
}

// vim: set ts=4 sw=4 et:
