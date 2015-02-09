import leon.lang._
import leon.collection._

object Lists5 {
  abstract class Option[T]
  case class Some[T](value: T) extends Option[T]
  case class None[T]() extends Option[T]

  def find[T](f: T => Boolean, list: List[T]): Option[T] = list match {
    case Cons(head, tail) => if (f(head)) Some(head) else find(f, tail)
    case Nil() => None()
  }

  def exists[T](f: T => Boolean, list: List[T]): Boolean = list match {
    case Cons(head, tail) => f(head) || exists(f, tail)
    case Nil() => false
  }

  def equivalence_lemma[T](f: T => Boolean, list: List[T]): Boolean = {
    find(f, list) match {
      case Some(e) => exists(f, list)
      case None() => !exists(f, list)
    }
  }

  def equivalence_lemma_induct[T](f: T => Boolean, list: List[T]): Boolean = {
    list match {
      case Cons(head, tail) => equivalence_lemma(f, list) && equivalence_lemma_induct(f, tail)
      case Nil() => equivalence_lemma(f, list)
    }
  }.holds
}
