import leon.lang._

object Lists {
  abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def exists(list: List, f: Int => Boolean): Boolean = list match {
    case Cons(head, tail) => f(head) || exists(tail, f)
    case Nil() => false
  }

  def forall(list: List, f: Int => Boolean): Boolean = list match {
    case Cons(head, tail) => f(head) && forall(tail, f)
    case Nil() => true
  }

  def exists_lemma(list: List, f: Int => Boolean): Boolean = {
    exists(list, f) == !forall(list, x => !f(x))
  }

  def exists_lemma_induct(list: List, f: Int => Boolean): Boolean = {
    list match {
      case Nil() => exists_lemma(list, f)
      case Cons(head, tail) => exists_lemma(list, f) && exists_lemma_induct(tail, f)
    }
  }.holds

}

// vim: set ts=4 sw=4 et:
