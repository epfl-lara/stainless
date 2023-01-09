import stainless.lang._
import stainless.collection._

object Candidate1 {
  def check(element: Int, l: List[Int]): Boolean = {
    decreases(l)
    l match {
      case Nil()        => false
      case Cons(hd, tl) => if (element == hd) true else check(element, tl)
    }
  }

  def app(l1: List[Int], l2: List[Int]): List[Int] = {
    decreases(l1)
    l1 match {
      case Nil() => l2
      case Cons(hd, tl) =>
        if (check(hd, l2)) app(tl, l2) else app(tl, l2 ++ List(hd))
    }
  }

  def uniq(lst: List[Int]): List[Int] = app(lst, Nil())
}
