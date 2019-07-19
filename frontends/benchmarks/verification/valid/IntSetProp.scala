import stainless.lang._
import stainless.annotation._

import scala.language.postfixOps

object IntSetProp {
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

    def P1(x: Int): Boolean = {
      !(Empty() contains x)
    }.holds

    def P2(s: IntSet, x: Int): Boolean = {
      (s incl x) contains x
    } holds because (s match {
      case Empty() => true
      case Node(left, elem, right) =>
        if (x < elem) P2(left, x)
        else if (x > elem) P2(right, x)
        else true
    })

    def P3(s: IntSet, x: Int,  y: Int): Boolean = {
      require(x != y)
      ((s incl x) contains y) == (s contains y)
    } holds because (s match {
      case Empty() => true
      case Node(left, elem, right) =>
        if (x < elem) P3(left, x, y)
        else if (x > elem) P3(right, x, y)
        else true
    })
  }
}
