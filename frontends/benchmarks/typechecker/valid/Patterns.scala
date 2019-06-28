import stainless.lang._
import stainless.collection._

object Patterns {

  sealed abstract class Pattern
  case object Empty extends Pattern
  case class Character(c: Char) extends Pattern
  case class Plus(left: Pattern, right: Pattern) extends Pattern
  case class Times(left: Pattern, right: Pattern) extends Pattern
  case class Star(pat: Pattern) extends Pattern

  def acc(p: Pattern, chars: List[Char], k: List[Char] => Boolean): Boolean = {
    decreases(p)
    p match {
      case Empty => k(chars)
      case Character(c) => chars match {
        case Cons(x, xs) if c == x => k(xs)
        case _ => false
      }
      case Plus(p1, p2) => if (acc(p1, chars, k)) true else acc(p2, chars, k)
      case Times(p1, p2) => acc(p1, chars, cs => acc(p2, cs, k))
      case Star(p) =>
        if (k(chars)) true
        else acc(p, chars, cs => if (cs.size == chars.size) false else acc(p, cs, k))
    }
  }
}
