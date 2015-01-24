import leon.lang._

object Lists2 {
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

  def positive_lemma(list: List[Int]): Boolean = {
    positive(list) == forall(list, (x: Int) => x >= 0)
  }

  def positive_lemma_induct(list: List[Int]): Boolean = {
    list match {
      case Nil() => positive_lemma(list)
      case Cons(head, tail) => positive_lemma(list) && positive_lemma_induct(tail)
    }
  }.holds

  def remove[T](list: List[T], e: T) : List[T] = {
    list match {
      case Nil() => Nil()
      case Cons(x, xs) if x == e => remove(xs, e)
      case Cons(x, xs)           => Cons(x, remove(xs, e))
    }
  } //ensuring { (res: List[T]) => forall(res, (x : T) => x != e) }

  def remove_lemma[T](list: List[T], e: T): Boolean = {
    forall(remove(list, e), (x : T) => x != e)
  }

  def remove_lemma_induct[T](list: List[T], e: T): Boolean = {
    list match {
      case Nil() => remove_lemma(list, e)
      case Cons(head, tail) => remove_lemma(list, e) && remove_lemma_induct(tail, e)
    }
  }.holds
}

// vim: set ts=4 sw=4 et:
