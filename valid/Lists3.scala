import leon.lang._

object Lists3 {
  abstract class List[T]
  case class Cons[T](head: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  def forall[T](list: List[T], f: T => Boolean): Boolean = list match {
    case Cons(head, tail) => f(head) && forall(tail, f)
    case Nil() => true
  }

  def positive(list: List[Int]): Boolean = list match {
    case Cons(head, tail) => if (head < 0) false else positive(tail)
    case Nil() => true
  }

  def gt(i: Int): Int => Boolean = x => x > i

  def gte(i: Int): Int => Boolean = x => gt(i)(x) || x == i

  def positive_lemma(list: List[Int]): Boolean = {
    positive(list) == forall(list, gte(0))
  }

  def positive_lemma_induct(list: List[Int]): Boolean = {
    list match {
      case Nil() => positive_lemma(list)
      case Cons(head, tail) => positive_lemma(list) && positive_lemma_induct(tail)
    }
  }.holds
}

// vim: set ts=4 sw=4 et:
