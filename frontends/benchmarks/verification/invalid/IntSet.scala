import stainless.lang._
import stainless.annotation._

object IntSet {
  case class Empty() extends IntSet
  case class Node(left: IntSet,
                  elem: Int,
                  right: IntSet) extends IntSet

  sealed abstract class IntSet {
    def incl(x: Int): IntSet = this match {
      case Empty() => Node(Empty(), x, Empty())
      case Node(left, elem, right) =>
        if (x < elem) Node(left.incl(x), elem, right)
        else if (x > elem) Node(left, elem, right.incl(x))
        else this
    }

    def contains(x: Int): Boolean = this match {
      case Empty() => false
      case Node(left, elem, right) =>
        if (x < elem) left.contains(x)
        else if (x > elem) right.contains(x)
        else true
    }

    def union(other: IntSet): IntSet = this match {
      case Empty() => other
      case Node(left, x, right) =>
        (left.union(right.union(other))).incl(x)
    }

    // FALSE
    def P4(t1: IntSet, t2: IntSet, x: Int,
           u: IntSet, xu: Boolean, x1: Boolean, x2: Boolean): Unit = {
      require(u == (t1.union(t2)) &&
        (x1 == (t1.contains(x))) &&
        (x2 == (t2.contains(x))) &&
        (xu == (u.contains(x))) && 0 < x && x < 10)
      ()
    }.ensuring(_ => ((t1.union(t2)).contains(x)) ==
      (t1.contains(x)) || (t2.contains(x)))
    /*
    [Warning ]  => INVALID
    [Warning ] Found counter-example:
    [Warning ]   t1: IntSet  -> Node( Node(Empty(), 1, Empty()), 0, Empty())
    [Warning ]   x: Int      -> 1
    [Warning ]   u: IntSet   -> Node(Node(Empty(), 0, Empty()), 1, Empty())
    [Warning ]   x2: Boolean -> false
    [Warning ]   x1: Boolean -> false
    [Warning ]   t2: IntSet  -> Empty()
    [Warning ]   xu: Boolean -> true
    */

  }
}
