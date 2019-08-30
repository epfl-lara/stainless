/**
 * NOTE: This test won't run with the current stainless configuration
 *       as the proofs in the function bodies will be simplified away!
 */

import stainless.lang._
import stainless.annotation._

object IntSet {
  case class Empty() extends IntSet
  case class Node(left: IntSet,
                  elem: Int,
                  right: IntSet) extends IntSet

  sealed abstract class IntSet {
    def incl(x: Int): IntSet = {
      decreases(this)
      this match {
        case Empty() => Node(Empty(),x,Empty())
        case Node(left, elem, right) =>
          if (x < elem) Node(left incl x, elem, right)
          else if (x > elem) Node(left, elem, right incl x)
          else this
      }
    }

    def contains(x: Int): Boolean = {
      decreases(this)
      this match {
        case Empty() => false
        case Node(left, elem, right) =>
          if (x < elem) left contains x
          else if (x > elem) right contains x
          else true
      }
    }

    def P1(x: Int): Boolean = {
      true
    } ensuring(_ => !(Empty() contains x))

    def P2(s: IntSet, x: Int): Boolean = {
      decreases(s)
      s match {
        case Empty() => true
        case Node(left, elem, right) =>
          if (x < elem) P2(left, x)
          else if (x > elem) P2(right, x)
          else true
      }
    } ensuring(_ => (s incl x) contains x)

    def P3(s: IntSet, x: Int,  y: Int): Boolean = {
      require(x != y)
      decreases(s)
      s match {
        case Empty() => true
        case Node(left, elem, right) =>
          if (x < elem) P3(left, x, y)
          else if (x > elem) P3(right, x, y)
          else true
      }
    } ensuring(_ =>  ((s incl x) contains y)==(s contains y))
  }
}
