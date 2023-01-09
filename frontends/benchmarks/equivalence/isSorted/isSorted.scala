import stainless.annotation._
import stainless.lang._
import stainless.collection._
import stainless.proof._

object IsSorted {

  def isSortedR(l: List[Int]): Boolean = {
    def loop(p: Int, l: List[Int]): Boolean = l match {
      case Nil() => true
      case Cons(x, xs) if (p <= x) => loop(x, xs)
      case _ => false
    }
    if (l.isEmpty) true
    else loop(l.head, l.tail)
  }

  def isSortedA(l: List[Int]): Boolean = {
    def leq(cur: Int, next: Int): Boolean = cur < next
    def iter(l: List[Int]): Boolean =
      if (l.isEmpty) true
      else if (l.tail.isEmpty) true
      else leq(l.head, l.tail.head) && iter(l.tail)
    if (l.size < 2) true
    else l.head <= l.tail.head && iter(l.tail)
  }

  def isSortedB(l: List[Int]): Boolean = {
    if (l.isEmpty)
      true
    else if (!l.tail.isEmpty && l.head > l.tail.head)
      false
    else
      isSortedB(l.tail)
  }

  def isSortedC(l: List[Int]): Boolean = {
    def chk(l: List[Int], p: Int, a: Boolean): Boolean = {
      if (l.isEmpty) a
      else if (l.head < p) false
      else chk(l.tail, l.head, a)
    }
    if (l.isEmpty) true
    else chk(l, l.head, true)
  }

}