import stainless.collection._
import stainless.lang._

object Candidate {
  def fold(f: (Int, Int) => Int, l: List[Int], a: Int): Int = {
    decreases(l)
    l match {
      case Nil()        => a
      case Cons(hd, tl) => f(hd, fold(f, tl, a))
    }
  }

  def max(lst: List[Int]): Int = {
    lst match {
      case Nil() => choose((x: Int) => true)
      case Cons(hd, tl) =>
        fold(
          (x, y) => if (x > y) x else y,
          lst,
          hd
        )
      }
  }

}
