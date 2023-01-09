import stainless.collection._
import stainless.lang._

object Candidate3 {
  def max(l: List[Int]): Int = {
    decreases(l)
    l match {
      case Nil() => Integer.MIN_VALUE
      case Cons(hd, tl) => {
        tl match {
          case Nil() => hd
          case Cons(hd1, tl1) =>
            if (hd > hd1) max(hd :: tl1) else max(hd1 :: tl1)
        }
      }
    }
  }
}
