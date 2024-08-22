/**
 * NOTE: This test won't run with the current stainless configuration
 *       as the proofs in the function bodies will be simplified away!
 */

import stainless.lang._
import stainless.annotation._

object IntSetInv {
  case class Empty() extends IntSet
  case class Node(left: IntSet,
                  elem: Int,
                  right: IntSet) extends IntSet {
      require(forall((x:Int) =>
                     (left.content.contains(x) ==> x < elem)) &&
              forall((x:Int) =>
                     (right.content.contains(x) ==> elem < x)))
  }

  sealed abstract class IntSet {
      def content: Set[Int] = this match {
          case Empty() => Set()
          case Node(left, elem, right) =>
            left.content ++ Set(elem) ++ right.content
      }

      def incl(x: Int): IntSet = { this match {
          case Empty() => Node(Empty(),x,Empty())
          case Node(left, elem, right) =>
            if (x < elem) Node(left.incl(x), elem, right)
            else if (x > elem) Node(left, elem, right.incl(x))
            else this
      }}.ensuring(res => res.content == this.content ++ Set(x))

      def contains(x: Int): Boolean = {this match {
          case Empty() => false
          case Node(left, elem, right) =>
            if (x < elem) left.contains(x)
            else if (x > elem) right.contains(x)
            else true
      }}.ensuring(res => (res == (this.content.contains(x))))

      def union(s: IntSet): IntSet = (this match {
        case Empty() => s
        case Node(left, x, right) => (left.union((right.union(s)))).incl(x)
      }).ensuring (res => res.content == this.content ++ s.content)

      def P1(x: Int): Unit =
      ().ensuring(_ => !(Empty().contains(x)))

      def P2(s: IntSet, x: Int): Unit =
      ().ensuring(_ => (s.incl(x)).contains(x))

      def P3(s: IntSet, x: Int,  y: Int): Unit = {
        require(x != y)
     }.ensuring(_ =>  ((s.incl(x)).contains(y))==(s.contains(y)))

      def P4(t1: IntSet, t2: IntSet, x: Int): Unit =
      ().ensuring (_ => (((t1.union(t2)).contains(x)) == (t1.contains(x))) || (t2.contains(x)))
  }
}
