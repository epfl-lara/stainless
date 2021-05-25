import stainless.lang._
import stainless.annotation._


object CastCorrectness {

  sealed abstract class List[@mutable T]
  case class Nil[@mutable T]() extends List[T]
  case class Cons[@mutable T](var head: T, var tail: List[T]) extends List[T]
  
  @pure
  def contains(self: List[Int], t: Int): Boolean =
    contents(freshCopy(self)).contains(t)

  @pure
  def contents(self: List[Int]): Set[Int] = {
    decreases(self)
    self match {
      case Nil() => Set.empty
      case Cons(head, tail) => contents(freshCopy(tail)) + head
    }
  }

  @pure
  def remove(self: List[Int], t: Int): List[Int] = {
    self match {
      case Nil() => freshCopy(Nil[Int]())
      case Cons(head, tail) if head == t => freshCopy(remove(tail, t))
      case Cons(head, tail) => freshCopy(Cons[Int](head, remove(tail, t)))
    }
  } ensuring {
    (ret: List[Int]) =>
      !contains(freshCopy(ret), t) &&
        contents(freshCopy(ret)).subsetOf(contents(freshCopy(self)))
  }

  @pure
  def remove_from_list(var0: List[Int]): Unit = {
    var list: List[Int] = freshCopy(var0)
    list match {
      case Cons(first_elem, _) =>
        list = remove(list, first_elem)
        if (contains(list, first_elem)) {
          error[Nothing]("still contained")
        }
      case _ => ()
    }
  }
}