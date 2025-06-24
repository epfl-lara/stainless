import stainless.lang._
import stainless.collection._

// This tests the normalization function where the return type is changed

object Model:

  def binSum(l1: List[Boolean], l2: List[Boolean], c: Boolean): List[Boolean] =
    (l1, l2) match
      case (Nil(), Nil()) => Nil()
      case (Cons(true, t1), Cons(false, t2)) => !c::binSum(t1, t2, c)
      case (Cons(false, t1), Cons(true, t2)) => !c::binSum(t1, t2, c)
      case (Cons(false, t1), Cons(false, t2)) => c::binSum(t1, t2, false)
      case (Cons(true, t1), Cons(true, t2)) => c::binSum(t1, t2, true)
      case (Cons(true, t1), Nil()) => !c::binSum(t1, Nil(), c)
      case (Cons(false, t1), Nil()) => c::binSum(t1, Nil(), false)
      case (Nil(), Cons(true, t2)) => !c::binSum(t2, Nil(), c)
      case (Nil(), Cons(false, t2)) => c::binSum(t2, Nil(), false)

  def norm(l1: List[Boolean], l2: List[Boolean], c: Boolean, res: List[Boolean]) =
    listToInt(res) // transform the semi-specified output to absorb trailing 0s
  def listToInt(l: List[Boolean]): BigInt = l match
    case Nil() => 0
    case Cons(true, tl) => 1 + 2 * listToInt(tl)
    case Cons(false, tl) => 2 * listToInt(tl)