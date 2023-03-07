import stainless.collection._
import stainless.lang._

// This is not expected to verify (it should timeout)
// but here we ensure that the `choose` functions (created from the `choose((x: Int) => true)`)
// for the Model and the Candidate do not get matched because it would make the type-checker unhappy
// (because we would create `choose` expressions when doing the replacement).
object Model {
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

  def norm(l: List[Int], f: Int): Int = {
    if (l.isEmpty) -1
    else f
  }
}
