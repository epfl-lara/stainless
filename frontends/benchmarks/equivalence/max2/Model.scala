import stainless.collection._
import stainless.lang._

object Model {

  def max(lst: List[Int]): Int = {
    decreases(lst)
    lst match {
      case Nil()           => Integer.MIN_VALUE
      case Cons(hd, Nil()) => hd
      case Cons(hd, tl)    => if (hd > max(tl)) hd else max(tl)
    }
  }

  def norm(l: List[Int], f: Int): Int = {
    if (l.isEmpty) -1
    else f
  }
}
