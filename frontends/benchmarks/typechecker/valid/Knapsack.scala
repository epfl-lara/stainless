import stainless._
import lang._
import annotation._
import math._

object Knapsack {
  sealed abstract class IList {
    def size: BigInt = {
      decreases(this)
      this match {
        case Cons(_, tail) => 1 + tail.size
        case Nil() => BigInt(0)
      }
    } ensuring(_ >= 0)
  }
  case class Cons(x: (BigInt, BigInt), tail: IList) extends IList { // a list of pairs of weights and values
    @extern
    override def toString: String = {
      decreases(this)
      if(tail == Nil()) x.toString
      else x.toString + "," + tail.toString
    }
  }
  case class Nil() extends IList {
    @extern
    override def toString = ""
  }

  def maxValue(items: IList, w: BigInt, currList: IList): BigInt = {
    require(w >= 0)
    decreases(w, currList.size, 0)
    currList match {
      case Cons((wi, vi), tail) =>
        val oldMax = maxValue(items, w, tail)
        if (wi <= w && wi > 0) {
          val choiceVal = vi + knapSack(w - wi, items)
          if (choiceVal >= oldMax)
            choiceVal
          else
            oldMax
        } else oldMax
      case Nil() => BigInt(0)
    }
  }

  def knapSack(w: BigInt, items: IList): BigInt = {
    require(w >= 0)
    decreases(w, items.size, 1)
    if (w == 0) BigInt(0)
    else {
      maxValue(items, w, items)
    }
  }

  def bottomup(w: BigInt, items: IList): IList = {
    require(w >= 0)
    decreases(w)
    if (w == 0)
      Cons((w, knapSack(w, items)), Nil())
    else {
      val tail = bottomup(w - 1, items)
      Cons((w, knapSack(w, items)), tail)
    }
  }

  /**
   * Computes the list of optimal solutions of all weights up to 'w'
   */
  def knapSackSol(w: BigInt, items: IList) = {
    require(w >= 0)
    bottomup(w, items)
  }
}
