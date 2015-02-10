import leon.lang._
import leon.collection._

object FlatMap {

  def append[T](l1: List[T], l2: List[T]): List[T] = l1 match {
    case Cons(head, tail) => Cons(head, append(tail, l2))
    case Nil() => l2
  }

  def associative_append_lemma[T](l1: List[T], l2: List[T], l3: List[T]): Boolean = {
    append(append(l1, l2), l3) == append(l1, append(l2, l3))
  }

  def associative_append_lemma_induct[T](l1: List[T], l2: List[T], l3: List[T]): Boolean = {
    l1 match {
      case Nil() => associative_append_lemma(l1, l2, l3)
      case Cons(head, tail) => associative_append_lemma(l1, l2, l3) && associative_append_lemma_induct(tail, l2, l3)
    }
  }.holds

  def flatMap[T,U](list: List[T], f: T => List[U]): List[U] = list match {
    case Cons(head, tail) => append(f(head), flatMap(tail, f))
    case Nil() => Nil()
  }

  def associative_lemma[T,U,V](list: List[T], f: T => List[U], g: U => List[V]): Boolean = {
    flatMap(flatMap(list, f), g) == flatMap(list, (x: T) => flatMap(f(x), g))
  }

  def associative_lemma_induct[T,U,V](list: List[T], flist: List[U], glist: List[V], f: T => List[U], g: U => List[V]): Boolean = {
    associative_lemma(list, f, g) &&
    append(glist, flatMap(append(flist, flatMap(list, f)), g)) == append(append(glist, flatMap(flist, g)), flatMap(list, (x: T) => flatMap(f(x), g))) &&
    (glist match {
      case Cons(ghead, gtail) =>
        associative_lemma_induct(list, flist, gtail, f, g)
      case Nil() => flist match {
        case Cons(fhead, ftail) =>
          associative_lemma_induct(list, ftail, g(fhead), f, g)
        case Nil() => list match {
          case Cons(head, tail) => associative_lemma_induct(tail, f(head), Nil(), f, g)
          case Nil() => true
        }
      }
    })
  }.holds

}
