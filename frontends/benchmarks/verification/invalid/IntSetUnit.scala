import stainless.lang._
import stainless.annotation._

object IntSetUnit {
  case class Empty() extends IntSet
  case class Node(left: IntSet,
                  elem: Int,
                  right: IntSet) extends IntSet
  sealed abstract class IntSet {
      def incl(x: Int): IntSet = this match {
          case Empty() => Node(Empty(),x,Empty())
          case Node(left, elem, right) =>
            if (x < elem) Node(left incl x, elem, right)
            else if (x > elem) Node(left, elem, right incl x)
            else this
      }
      def contains(x: Int): Boolean = this match {
          case Empty() => false
          case Node(left, elem, right) =>
            if (x < elem) left contains x
            else if (x > elem) right contains x
            else true
      }

     def union(other: IntSet): IntSet = this match {
          case Empty() => other
          case Node(left, x, right) =>
              (left union (right union other)) incl x
      }

      def P4(t1: IntSet, t2: IntSet, x: Int): Unit = {
        ()
      } ensuring(_ =>  ((t1 union t2) contains x)==
                        (t1 contains x) || (t2 contains x))
  /*
  [  Info  ]  - Now considering 'postcondition' VC for P4 @?:?...
  [Warning ]  => INVALID
  [Warning ] Found counter-example:
  [Warning ]   x: Int     -> 13384454
  [Warning ]   t1: IntSet -> Node(Node(Empty(), 13384454, Empty()), 101057, Empty())
  [Warning ]   t2: IntSet -> Empty()
  */

  }
}
