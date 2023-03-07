import stainless.annotation._
import stainless.lang._
import stainless.collection._
import stainless.proof._ 

object Uniq {

  def uniqR(lst: List[Int]): List[Int] = {

    def find(lst: List[Int], n: Int): Boolean = lst match {
      case Nil()        => false
      case Cons(hd, tl) => (n == hd) || find(tl, n)
    }

    def unique(l: List[Int], r: List[Int]): List[Int] =
      l match {
        case Nil() => r
        case Cons(hd, tl) =>
          if (!find(r, hd)) unique(tl, r ++ List(hd))
          else unique(tl, r)
      }

    unique(lst, Nil())

  }

  def uniqA(lst: List[Int]): List[Int] = {

    def isin(lst: List[Int], a: Int): Boolean = 
    lst.foldRight(false){ (e, acc) => (e == a || acc) }

    def distinct(a: List[Int], b: List[Int]): List[Int] =
      a match {
        case Nil() => b
        case Cons(hd, tl) =>
          if (isin(b, hd)) distinct(tl, b)
          else distinct(tl, b ++ List[Int](hd))
      }

    distinct(lst, List())

  }

}