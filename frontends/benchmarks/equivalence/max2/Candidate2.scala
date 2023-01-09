import stainless.collection._
import stainless.lang._

object Candidate2 {
  def max(l: List[Int]): Int = {
    decreases(l)
    l match {
      case Nil()      => Integer.MIN_VALUE
      case Cons(h, t) => if (h > max(t)) h else max(t)
    }
  }
}
