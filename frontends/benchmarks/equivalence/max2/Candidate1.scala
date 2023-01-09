import stainless.collection._
import stainless.lang._

object Candidate1 {
  def max(l: List[Int]): Int = {
    decreases(l)
    l match {
      case Nil()           => 42
      case Cons(hd, Nil()) => hd
      case Cons(hd, tl)    => if (hd > max(tl)) hd else max(tl)
    }
  }
}
