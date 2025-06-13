import stainless.lang._
import stainless.collection._

object Candidate:

  def binSum(l1: List[Boolean], l2: List[Boolean], c: Boolean): List[Boolean] =
    (l1, l2, c) match
      case (Nil(), Nil(), _) => List(false)
      case (Cons(true, t1), Cons(false, t2), false) => true::binSum(t1, t2, false)
      case (Cons(true, t1), Cons(false, t2), true) => false::binSum(t1, t2, true)
      case (Cons(false, t1), Cons(true, t2), false) => true::binSum(t1, t2, false)
      case (Cons(false, t1), Cons(true, t2), true) => false::binSum(t1, t2, true)
      case (Cons(false, t1), Cons(false, t2), false) => false::binSum(t1, t2, false)
      case (Cons(false, t1), Cons(false, t2), true) => true::binSum(t1, t2, false)
      case (Cons(true, t1), Cons(true, t2), false) => false::binSum(t1, t2, true)
      case (Cons(true, t1), Cons(true, t2), true) => true::binSum(t1, t2, true)
      case (Cons(true, t1), Nil(), true) => false::binSum(t1, Nil(), true)
      case (Cons(true, t1), Nil(), false) => true::binSum(t1, Nil(), false)
      case (Cons(false, t1), Nil(), true) => true::binSum(t1, Nil(), false)
      case (Cons(false, t1), Nil(), false) => false::binSum(t1, Nil(), false)
      case (Nil(), Cons(true, t1), true) => false::binSum(t1, Nil(), true)
      case (Nil(), Cons(true, t1), false) => true::binSum(t1, Nil(), false)
      case (Nil(), Cons(false, t1), true) => true::binSum(t1, Nil(), false)
      case (Nil(), Cons(false, t1), false) => false::binSum(t1, Nil(), false)