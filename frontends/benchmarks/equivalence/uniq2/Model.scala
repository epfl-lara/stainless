import stainless.collection._
import stainless.annotation._
import stainless.lang._

object Model {

  def remove_elem_1(e: Int, lst: List[Int]): List[Int] = {
    decreases(lst)
    lst match {
      case Nil() => Nil()
      case Cons(hd, tl) =>
        if (e == hd) remove_elem_1(e, tl) else hd :: remove_elem_1(e, tl)
    }
  }

  def solution_1(lst: List[Int]): List[Int] = {
    decreases(lst)
    lst match {
      case Nil()        => Nil()
      case Cons(hd, tl) => hd :: remove_elem_1(hd, solution_1(tl))
    }
  }

  def drop_2(lst: List[Int], n: Int): List[Int] = {
    decreases(lst)
    lst match {
      case Nil()        => Nil()
      case Cons(hd, tl) => if (hd == n) drop_2(tl, n) else hd :: drop_2(tl, n)
    }
  }

  def lemma_2(n: Int, @induct lst: List[Int]): Unit = {
  } ensuring(drop_2(lst, n).size <= lst.size)

  def solution_2(lst: List[Int]): List[Int] = {
    decreases(lst.size)

    def lem(n: Int, @stainless.annotation.induct lst: List[Int]): Unit = {
      ()
    } ensuring(drop_2(lst, n).size <= lst.size)

    lst match {
      case Nil()        => Nil()
      case Cons(hd, tl) =>
        lem(hd, tl)
        hd :: solution_2(drop_2(tl, hd))
    }
  }

  def is_in_3(lst: List[Int], a: Int): Boolean = {
    decreases(lst)
    lst match {
      case Nil()        => false
      case Cons(hd, tl) => if (a == hd) true else is_in_3(tl, a)
    }
  }

  def unique_3(lst1: List[Int], lst2: List[Int]): List[Int] = {
    decreases(lst1)
    lst1 match {
      case Nil() => lst2
      case Cons(hd, tl) =>
        if (is_in_3(lst2, hd)) unique_3(tl, lst2) else unique_3(tl, lst2 ++ List[Int](hd))
    }
  }

  def solution_3(lst: List[Int]): List[Int] = { unique_3(lst, Nil()) }

  def solution_4(lst: List[Int]): List[Int] = {

    def isNotIn_4(tlst: List[Int], c: Int): Boolean = {
      decreases(tlst)
      tlst match {
        case Nil()        => true
        case Cons(hd, tl) => if (hd == c) false else true && isNotIn_4(tl, c)
      }
    }

    def uniqSave_4(l1: List[Int], l2: List[Int]): List[Int] = {
      decreases(l1)
      l1 match {
        case Nil() => { l2 }
        case Cons(hd, tl) =>
          if (isNotIn_4(l2, hd)) {
            uniqSave_4(tl, l2 ++ List(hd))
          } else {
            uniqSave_4(tl, l2)
          }
      }
    }
    uniqSave_4(lst, Nil())

  }

}